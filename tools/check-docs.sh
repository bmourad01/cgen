#!/bin/sh

set -eu

root="${1:-_build/default/_doc/_html}"
if [ ! -d "$root" ]; then
    echo "check-docs: no such directory: $root" >&2
    exit 2
fi

dead=$(mktemp)
allow=$(mktemp)
trap 'rm -f "$dead" "$allow"' EXIT

find "$root" -name '*.html' | while IFS= read -r page; do
    dir=${page%/*}
    grep -o 'href="[^"]*"' "$page" 2>/dev/null \
        | sed -e 's/^href="//' -e 's/"$//' \
        | while IFS= read -r href; do
        case "$href" in
            http://*|https://*|\#*|mailto:*|'') continue ;;
        esac
        rel=${href%%#*}
        [ -n "$rel" ] || continue
        [ -e "$dir/$rel" ] && continue
        case "$rel" in
            # insert "allow" cases here as-needed
            *) echo "$rel" >>"$dead" ;;
        esac
    done
done

n_allow=$(wc -l <"$allow" | tr -d ' ')
n_dead=$(wc -l <"$dead" | tr -d ' ')

echo "check-docs: scanned $root"
if [ "$n_allow" -gt 0 ]; then
    echo "check-docs: $n_allow allowlisted dead link(s):"
    sort "$allow" | uniq -c | sed 's/^/  [ok]  /'
fi
if [ "$n_dead" -gt 0 ]; then
    echo "check-docs: FAIL, $n_dead unexpected dead link(s):" >&2
    sort "$dead" | uniq -c | sed 's/^/  [DEAD]/' >&2
    exit 1
fi
echo "check-docs: OK, no unexpected dead links"
