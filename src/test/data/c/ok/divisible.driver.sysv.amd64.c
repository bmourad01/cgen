#include <assert.h>

extern int s_div3(int x);
extern int s_div4(int x);
extern int s_div100(int x);
extern int s_ndiv7(int x);
extern unsigned u_div6(unsigned x);
extern unsigned u_div10(unsigned x);
extern unsigned u_mod7(unsigned x);
extern unsigned u_mod641(unsigned x);

int
main(void) {
  assert(s_div3(0) && s_div3(9) && s_div3(-9) && s_div3(-3));
  assert(!s_div3(1) && !s_div3(-1) && !s_div3(-8) && !s_div3(7));
  assert(s_div4(0) && s_div4(8) && s_div4(-8) && s_div4(-4));
  assert(!s_div4(-3) && !s_div4(7) && !s_div4(-1));
  assert(s_div100(0) && s_div100(100) && s_div100(-100) && s_div100(-200));
  assert(!s_div100(50) && !s_div100(-150) && !s_div100(-99));
  assert(!s_ndiv7(0) && !s_ndiv7(14) && !s_ndiv7(-14));
  assert(s_ndiv7(1) && s_ndiv7(-13) && s_ndiv7(8));
  assert(u_div6(0) && u_div6(6) && u_div6(12) && u_div6(4294967292u));
  assert(!u_div6(7) && !u_div6(4u) && !u_div6(4294967295u));
  assert(u_div10(0) && u_div10(10) && u_div10(4294967290u));
  assert(!u_div10(4294967295u) && !u_div10(3u));
  assert(u_mod7(0) == 0 && u_mod7(20) == 6);
  assert(u_mod7(4294967295u) == 4294967295u % 7u);
  assert(u_mod7(4294967289u) == 4294967289u % 7u);
  assert(u_mod641(0) == 0 && u_mod641(641) == 0 && u_mod641(642) == 1);
  assert(u_mod641(4294967295u) == 4294967295u % 641u);
  return 0;
}
