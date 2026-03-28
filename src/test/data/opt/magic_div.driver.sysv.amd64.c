#include <assert.h>
#include <limits.h>
#include <stdint.h>

struct magic_s {
  int m;
  int sh;
};
struct magic_u {
  unsigned m;
  unsigned add;
  unsigned sh;
};

struct magic_s magic_signed(int d);
struct magic_u magic_unsigned(unsigned d);

static int
apply_sdiv(int x, int d, struct magic_s mg) {
  int64_t t = (int64_t)x * (int64_t)mg.m;
  int q = (int)((uint64_t)t >> 32);
  if (d >= 0 && mg.m < 0)
    q += x;
  if (d < 0 && mg.m >= 0)
    q -= x;
  if (mg.sh > 0)
    q >>= mg.sh;
  q += (int)((unsigned)q >> 31);
  return q;
}

static unsigned
apply_udiv(unsigned x, struct magic_u mg) {
  uint64_t t = (uint64_t)x * (uint64_t)mg.m;
  unsigned q = (unsigned)(t >> 32);
  if (mg.add) {
    q = ((x - q) >> 1) + q;
    q >>= (mg.sh - 1);
  } else if (mg.sh > 0) {
    q >>= mg.sh;
  }
  return q;
}

int
main(void) {
  static const int sdivs[] = {2, 3, 5, 6, 7, 9, 10, 11, -3, -5, -7};
  static const int svals[] = {0,   1,   -1,   7,       -7,      14,
                              -14, 100, -100, INT_MAX, -INT_MAX};
  for (int i = 0; i < (int)(sizeof sdivs / sizeof sdivs[0]); i++) {
    int d = sdivs[i];
    struct magic_s mg = magic_signed(d);
    for (int j = 0; j < (int)(sizeof svals / sizeof svals[0]); j++) {
      int x = svals[j];
      assert(apply_sdiv(x, d, mg) == x / d);
    }
  }

  static const unsigned udivs[] = {3, 5, 6, 7, 9, 10, 11, 25, 100};
  static const unsigned uvals[] = {0,   1,   6,           7,          14,
                                   100, 999, 0x80000000u, 0xffffffffu};
  for (int i = 0; i < (int)(sizeof udivs / sizeof udivs[0]); i++) {
    unsigned d = udivs[i];
    struct magic_u mg = magic_unsigned(d);
    for (int j = 0; j < (int)(sizeof uvals / sizeof uvals[0]); j++) {
      unsigned x = uvals[j];
      assert(apply_udiv(x, mg) == x / d);
    }
  }

  return 0;
}
