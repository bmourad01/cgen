#include <assert.h>

extern unsigned u_div3(unsigned x);
extern int s_div4(int x);
extern int s_div100(int x);
extern int s_ndiv7(int x);
extern unsigned long u_div6(unsigned long x);

int
main(void) {
  assert(u_div3(0) && u_div3(9) && u_div3(3000000000u));
  assert(!u_div3(1) && !u_div3(3000000001u));

  /* signed power of two, including negatives. */
  assert(s_div4(0) && s_div4(-8) && s_div4(-4));
  assert(!s_div4(-3) && !s_div4(7));

  /* signed even non-power-of-two, including negatives. */
  assert(s_div100(0) && s_div100(100) && s_div100(-100) && s_div100(-200));
  assert(!s_div100(50) && !s_div100(-150));

  /* signed `!= 0`. */
  assert(!s_ndiv7(0) && !s_ndiv7(-14));
  assert(s_ndiv7(1) && s_ndiv7(-13));

  /* unsigned 64-bit, large dividends (6 * 3e18 = 1.8e19). */
  assert(u_div6(0) && u_div6(6) && u_div6(18000000000000000000ul));
  assert(!u_div6(7) && !u_div6(18000000000000000001ul));

  return 0;
}
