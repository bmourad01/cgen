#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

extern size_t cgen_strcspn(const char *s, const char *c);

static void
check_one(const char *s, const char *accept) {
  size_t got = cgen_strcspn(s, accept);
  assert((long)got >= 0);
  size_t exp = strcspn(s, accept);
  if (got != exp) {
    fprintf(
      stderr,
      "Mismatch!\n  s      = \"%s\"\n  accept = \"%s\"\n  got=%zu exp=%zu\n", s,
      accept, got, exp);
    assert(got == exp);
  }
}

static unsigned int
rng(unsigned int *state) {
  *state = (*state) * 1664525u + 1013904223u;
  return *state;
}

static void
random_string(char *out, size_t out_cap, unsigned int *st,
              const char *alphabet) {
  assert(out_cap > 0);
  size_t alpha_n = strlen(alphabet);
  size_t n = rng(st) % (out_cap - 1); // length in [0, out_cap-2]
  for (size_t i = 0; i < n; i++) {
    out[i] = alphabet[rng(st) % alpha_n];
  }
  out[n] = '\0';
}

int
main() {
  check_one("", "");
  check_one("", "a");
  check_one("a", "");
  check_one("abc", "");

  check_one("abc", "a"); // 0
  check_one("abc", "b"); // 1
  check_one("abc", "c"); // 2
  check_one("abc", "x"); // 3
  check_one("abc", "z"); // 3

  check_one("aaaaa", "a"); // 0
  check_one("aaaaa", "b"); // 5
  check_one("baaaa", "a"); // 1
  check_one("baaaa", "b"); // 0

  check_one("hello", "o");   // 4
  check_one("hello", "l");   // 2
  check_one("hello", "x");   // 5
  check_one("hello", "he");  // 0
  check_one("hello", "ol");  // 2
  check_one("hello", "xyz"); // 5

  check_one("abcdef", "xz");  // 6
  check_one("abcdef", "fx");  // 5
  check_one("abcdef", "fa");  // 0
  check_one("abcdef", "de");  // 3
  check_one("abcdef", "fed"); // 3

  check_one("0123456789", "7");   // 7
  check_one("0123456789", "987"); // 7
  check_one("0123456789", "x9");  // 9
  check_one("0123456789", "xyz"); // 10

  check_one("mississippi", "s");   // 2
  check_one("mississippi", "p");   // 8
  check_one("mississippi", "m");   // 0
  check_one("mississippi", "xyz"); // 11
  check_one("mississippi", "pi");  // 1

  check_one("abcdef", "xy");
  check_one("abcdef", "dx");
  check_one("abcdef", "za");
  check_one("banana", "nx");
  check_one("banana", "xy");

  {
    unsigned int st = 0xC0FFEEu;
    const char *alph_s = "abccddeeffgghhiijjkkllmmnnooppqqrrssttuvwxyz0123";
    const char *alph_a = "abcxyz0123";
    char s[128];
    char a[64];
    for (int i = 0; i < 50000; i++) {
      random_string(s, sizeof(s), &st, alph_s);
      random_string(a, sizeof(a), &st, alph_a);
      if ((rng(&st) % 10) == 0) {
        char c = alph_a[rng(&st) % strlen(alph_a)];
        a[0] = c;
        a[1] = '\0';
      }
      check_one(s, a);
    }
  }
}
