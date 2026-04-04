#include <assert.h>

extern int ping(int n);
extern int pong(int n);
extern int ping_nontail(int n);
extern int call_and_ignore(int n);
extern int dispatch(int x, int y);
extern int mixed_tail(int x, int y);
extern int gcd_tc(int a, int b);
extern int gcd_nt(int a, int b);
extern int sum7(int a, int b, int c, int d, int e, int f, int g);
extern int tail_sum7_stk(int a, int b, int c, int d, int e, int f, int g);

int
main(void) {
  assert(ping(0) == 0);
  assert(ping(1) == 1);
  assert(ping(2) == 0);
  assert(ping(3) == 1);
  assert(ping(100) == 0);
  assert(ping(101) == 1);

  assert(pong(0) == 1);
  assert(pong(1) == 0);
  assert(pong(100) == 1);

  assert(ping_nontail(0) == 0);
  assert(ping_nontail(1) == 1);
  assert(ping_nontail(2) == 0);

  assert(call_and_ignore(0) == 0);
  assert(call_and_ignore(5) == 5);

  assert(dispatch(2, 4) == ping(2));
  assert(dispatch(4, 2) == pong(2));
  assert(dispatch(0, 1) == ping(0));

  assert(mixed_tail(0, 3) == pong(3));
  assert(mixed_tail(1, 5) == ping(0));
  assert(mixed_tail(3, 0) == ping(2));

  assert(gcd_tc(12, 8) == 4);
  assert(gcd_tc(100, 75) == 25);
  assert(gcd_tc(7, 0) == 7);
  assert(gcd_tc(0, 5) == 5);

  assert(tail_sum7_stk(1, 2, 3, 4, 5, 6, 7) == 28);
  assert(tail_sum7_stk(0, 0, 0, 0, 0, 0, 42) == 42);

  assert(gcd_nt(12, 8) == 4);
  assert(gcd_nt(100, 75) == 25);
  assert(gcd_nt(7, 0) == 7);
  assert(gcd_nt(0, 5) == 5);

  return 0;
}
