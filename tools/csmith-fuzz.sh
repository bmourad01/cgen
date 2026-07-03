#!/usr/bin/env bash
#
# Differential-fuzzing harness for the cgen C frontend, using csmith.
#
# Each iteration generates a random (UB-free) C program with csmith, compiles
# it with both a reference compiler and cgen, runs both, and compares their
# output (csmith programs print a checksum of their final global state). The
# outcomes are classified:
#
#   pass       - cgen built it and its output matched the reference
#   compile    - cgen rejected it (a frontend coverage gap; clean diagnostic)
#   crash      - cgen raised an internal error / uncaught exception
#   asm        - cgen emitted asm that the assembler/linker rejected
#   runtime    - the cgen binary crashed or timed out
#   mismatch   - outputs differ (a miscompile)
#   ref        - the reference compiler or run failed (sample discarded)
#
# For every non-pass outcome a reproducer (the preprocessed C that cgen saw,
# plus error/output logs) is saved under <outdir>/<category>/<seed>/, the
# diagnostic is streamed live, and a ranked table of (normalized) diagnostics
# is printed at the end so the dominant frontend gap is obvious.
#
# Iterations run in parallel (--jobs workers); each worker uses a private work
# dir. The output dir is wiped at startup so the reproducer tree and the
# diagnostic ranking reflect only this run.
#
# cgen has no preprocessor, so we expand with `cc -E -P` against csmith's
# self-contained minimal runtime (no glibc), and hand cgen a *.c file (the
# .i extension would select the Virtual IR parser by default).
#
# The csmith flags are gated to the frontend's current coverage; widen them
# with --csmith-flags as gaps close.
#
# The exit status is non-zero iff a miscompile (mismatch) was found.

set -u

prog=$(basename "$0")

# Defaults
N="${CSMITH_ITERS:-50}"
JOBS="${JOBS:-$(nproc 2>/dev/null || echo 1)}"
CGEN="${CGEN:-cgen}"
CC="${CC:-cc}"
CSMITH="${CSMITH:-csmith}"
CSMITH_INCLUDE="${CSMITH_INCLUDE:-/usr/local/include}"
TIMEOUT="${TIMEOUT:-5}"
OUTDIR="${OUTDIR:-/tmp/cgen-csmith}"
CSMITH_FLAGS="${CSMITH_FLAGS:---no-volatiles --no-packed-struct --no-float --no-math64 --max-funcs 5}"
VERBOSITY="${VERBOSITY:-1}"

usage() {
    cat <<EOF
Differential-fuzz the cgen C frontend against a reference compiler with csmith.

Usage: $prog [options] [iterations]

Options:
  -n, --iters N           number of programs to generate (default: $N)
  -j, --jobs N            parallel workers (default: nproc)
  -t, --timeout SECS      per-program run timeout (default: $TIMEOUT)
  -o, --outdir DIR        reproducer / work directory, wiped at startup
                          (default: $OUTDIR)
      --cgen PATH         cgen binary under test (default: $CGEN)
      --cc PATH           reference C compiler (default: $CC)
      --csmith PATH       csmith binary (default: $CSMITH)
      --csmith-include D   csmith runtime header dir (default: $CSMITH_INCLUDE)
      --csmith-flags STR  csmith generation flags
                          (default: $CSMITH_FLAGS)
  -v, --verbose           log each per-program pipeline step
  -q, --quiet             only print the final summary
  -h, --help              show this help and exit

A bare positional argument is taken as the iteration count (so both
'$prog -n 200' and '$prog 200' work). Every option also has an environment
default (CSMITH_ITERS, JOBS, CGEN, CC, CSMITH, CSMITH_INCLUDE, TIMEOUT,
OUTDIR, CSMITH_FLAGS, VERBOSITY); an explicit option wins over the environment.

Outcome categories: pass, compile (frontend gap), crash (cgen internal error),
asm (bad asm), runtime (cgen binary crash/timeout), mismatch (miscompile),
ref (reference failed; discarded). Reproducers land in <outdir>/<category>/<seed>/.

Examples:
  $prog 200                       # 200 iterations, defaults otherwise
  $prog -n 500 -j 8               # 500 iterations across 8 workers
  $prog --cgen ./cgen.exe -v      # test a specific binary, verbose
EOF
}

die() { printf '%s: %s\n' "$prog" "$1" >&2; exit 2; }

is_uint() { [[ "$1" =~ ^[0-9]+$ ]]; }

getopt --test >/dev/null 2>&1
[[ $? -eq 4 ]] || die "the enhanced getopt(1) from util-linux is required"

parsed=$(getopt \
             -o 'n:j:t:o:vqh' \
             -l 'iters:,jobs:,timeout:,outdir:,cgen:,cc:,csmith:,csmith-include:,csmith-flags:,verbose,quiet,help' \
             -n "$prog" -- "$@") || { usage >&2; exit 2; }
eval set -- "$parsed"

while true; do
    case "$1" in
        -n|--iters)          N="$2";              shift 2;;
        -j|--jobs)           JOBS="$2";           shift 2;;
        -t|--timeout)        TIMEOUT="$2";        shift 2;;
        -o|--outdir)         OUTDIR="$2";         shift 2;;
        --cgen)              CGEN="$2";           shift 2;;
        --cc)                CC="$2";             shift 2;;
        --csmith)            CSMITH="$2";         shift 2;;
        --csmith-include)    CSMITH_INCLUDE="$2"; shift 2;;
        --csmith-flags)      CSMITH_FLAGS="$2";   shift 2;;
        -v|--verbose)        VERBOSITY=2;         shift;;
        -q|--quiet)          VERBOSITY=0;         shift;;
        -h|--help)           usage; exit 0;;
        --)                  shift; break;;
        *)                   die "unexpected option '$1'";;
    esac
done

# Remaining positional (if any) is the iteration count.
case $# in
    0) ;;
    1) N="$1";;
    *) die "unexpected extra arguments: $*";;
esac

is_uint "$N"       || die "iterations must be a non-negative integer, got '$N'"
is_uint "$JOBS"    || die "jobs must be a non-negative integer, got '$JOBS'"
is_uint "$TIMEOUT" || die "timeout must be a non-negative integer, got '$TIMEOUT'"
[[ "$JOBS" -ge 1 ]] || die "jobs must be at least 1"

command -v "$CSMITH" >/dev/null 2>&1 || die "csmith not found: '$CSMITH' (set --csmith)"
command -v "$CGEN"   >/dev/null 2>&1 || die "cgen not found: '$CGEN' (set --cgen)"
command -v "$CC"     >/dev/null 2>&1 || die "reference compiler not found: '$CC' (set --cc)"

export CGEN CC CSMITH CSMITH_INCLUDE TIMEOUT OUTDIR CSMITH_FLAGS VERBOSITY

rm -rf "$OUTDIR"; mkdir -p "$OUTDIR/work"

# A one-line, location- and identifier-normalized form of the first error in a
# log, so distinct instances of the same diagnostic collapse together.
extract_err() {
    grep -m1 -iE 'error' "$1" 2>/dev/null \
        | sed -E "s#^[^ ]*:[0-9][0-9:+-]*: ##; s/[0-9]+/N/g; s/\x27[^\x27]*\x27/X/g" \
        | tr -d '\t' | head -c 200
}
export -f extract_err

# save <workdir> <category> <seed> [extra files...]
save() {
    local w="$1" cat="$2" seed="$3"; shift 3
    local dir="$OUTDIR/$cat/$seed"; mkdir -p "$dir"
    cp "$w/pp.c" "$w/orig.c" "$dir/" 2>/dev/null
    for f in "$@"; do cp "$f" "$dir/" 2>/dev/null; done
}
export -f save

# run_one <seed>: full pipeline in a private work dir. Emits one TSV line
# `<category>\t<seed>\t<normalized-error>` on stdout (for aggregation), and
# streams the raw diagnostic / any mismatch to stderr (for live visibility).
run_one() {
    local seed="$1"
    local w="$OUTDIR/work/$seed"; mkdir -p "$w"
    local orig="$w/orig.c" pp="$w/pp.c" cat err

    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: generating\n' "$seed" >&2
    fi
    if ! "$CSMITH" $CSMITH_FLAGS --seed "$seed" -o "$orig" 2>/dev/null; then
        printf 'ref\t%s\t\n' "$seed"; rm -rf "$w"; return
    fi

    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: preprocessing\n' "$seed" >&2
    fi
    sed -i 's#include "csmith.h"#include "csmith_minimal.h"#' "$orig"
    if ! "$CC" -E -P -I"$CSMITH_INCLUDE" "$orig" -o "$pp" 2>/dev/null; then
        printf 'ref\t%s\t\n' "$seed"; rm -rf "$w"; return
    fi

    # Reference build + run. (-lm: cgen emits real `fabsf`/`fabs` calls where gcc
    # inlines them as builtins, so the linked program needs libm.)
    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: building reference\n' "$seed" >&2
    fi
    if ! "$CC" -w "$pp" -lm -o "$w/ref" 2>/dev/null \
            || ! timeout "$TIMEOUT" "$w/ref" > "$w/ref.out" 2>/dev/null; then
        printf 'ref\t%s\t\n' "$seed"; rm -rf "$w"; return
    fi

    # cgen: compile to asm.
    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: compiling with cgen\n' "$seed" >&2
    fi
    if ! "$CGEN" "$pp" -o "$w/cg.S" 2>"$w/cgen.err"; then
        if grep -q 'internal error\|uncaught exception' "$w/cgen.err"; then
            cat=crash; else cat=compile; fi
        err=$(extract_err "$w/cgen.err")
        save "$w" "$cat" "$seed" "$w/cgen.err"
        printf '  [%-7s] %s: %s\n' "$cat" "$seed" "$err" >&2
        printf '%s\t%s\t%s\n' "$cat" "$seed" "$err"; rm -rf "$w"; return
    fi

    # Assemble + link.
    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: assembling output of cgen\n' "$seed" >&2
    fi
    if ! "$CC" "$w/cg.S" -lm -o "$w/cg" 2>"$w/asm.err"; then
        err=$(extract_err "$w/asm.err")
        save "$w" asm "$seed" "$w/cg.S" "$w/asm.err"
        printf '  [%-7s] %s: %s\n' asm "$seed" "$err" >&2
        printf 'asm\t%s\t%s\n' "$seed" "$err"; rm -rf "$w"; return
    fi

    # Run + compare.
    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: running cgen-compiled program\n' "$seed" >&2
    fi
    if ! timeout "$TIMEOUT" "$w/cg" > "$w/cg.out" 2>/dev/null; then
        save "$w" runtime "$seed" "$w/cg.S"
        printf 'runtime\t%s\t\n' "$seed"; rm -rf "$w"; return
    fi
    if ! diff -q "$w/ref.out" "$w/cg.out" >/dev/null; then
        save "$w" mismatch "$seed" "$w/cg.S" "$w/ref.out" "$w/cg.out"
        printf '  !!! MISMATCH seed=%s -> %s/mismatch/%s\n' "$seed" "$OUTDIR" "$seed" >&2
        printf 'mismatch\t%s\t\n' "$seed"; rm -rf "$w"; return
    fi

    if [[ "$VERBOSITY" -gt 1 ]]; then
        printf '  %s: success\n' "$seed" >&2
    fi
    printf 'pass\t%s\t\n' "$seed"; rm -rf "$w"
}
export -f run_one

if [[ "$VERBOSITY" -ge 1 ]]; then
    printf 'csmith-fuzz: %d iterations | %d jobs | flags:%s | timeout %ss\n' \
           "$N" "$JOBS" "$CSMITH_FLAGS" "$TIMEOUT"
fi

results="$OUTDIR/results.tsv"; : > "$results"
seeds=()
for ((i = 0; i < N; i++)); do seeds+=( $(( (RANDOM << 15 ^ RANDOM) & 0x7fffffff )) ); done
if [[ ${#seeds[@]} -gt 0 ]]; then
    printf '%s\n' "${seeds[@]}" \
        | xargs -P "$JOBS" -n1 bash -c 'run_one "$1"' _ >> "$results"
fi

count_cat() { awk -F'\t' -v c="$1" '$1==c{n++} END{print n+0}' "$results"; }

echo "----------------------------------------"
printf '  pass     %4d\n' "$(count_cat pass)"
printf '  compile  %4d   (frontend gap)\n' "$(count_cat compile)"
printf '  crash    %4d   (cgen internal error)\n' "$(count_cat crash)"
printf '  asm      %4d   (bad asm)\n' "$(count_cat asm)"
printf '  runtime  %4d   (cgen binary crash/timeout)\n' "$(count_cat runtime)"
printf '  MISMATCH %4d   (miscompile)\n' "$(count_cat mismatch)"
printf '  ref      %4d   (reference failed; discarded)\n' "$(count_cat ref)"

if awk -F'\t' '$3!=""' "$results" | grep -q .; then
    echo "----------------------------------------"
    echo "Top diagnostics (count, normalized):"
    awk -F'\t' '$3!=""{print $3}' "$results" | sort | uniq -c | sort -rn | head -20 \
        | sed 's/^/  /'
fi
echo "  reproducers under: $OUTDIR/<category>/<seed>/"

# Non-zero exit if any miscompile was found.
[ "$(count_cat mismatch)" -eq 0 ]
