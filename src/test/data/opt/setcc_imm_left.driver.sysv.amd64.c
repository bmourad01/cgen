#include <assert.h>

extern int sgt(signed char *p);
extern int sge(signed char *p);
extern int ugt(unsigned char *p);
extern int uge(unsigned char *p);

int
main(void) {
  signed char s;
  unsigned char u;

  s = -11;
  assert(sgt(&s) == 2);
  s = -10;
  assert(sgt(&s) == 0);
  s = -9;
  assert(sgt(&s) == 0);

  s = 4;
  assert(sge(&s) == 2);
  s = 5;
  assert(sge(&s) == 2);
  s = 6;
  assert(sge(&s) == 0);

  u = 99;
  assert(ugt(&u) == 2);
  u = 100;
  assert(ugt(&u) == 0);
  u = 101;
  assert(ugt(&u) == 0);

  u = 99;
  assert(uge(&u) == 2);
  u = 100;
  assert(uge(&u) == 2);
  u = 101;
  assert(uge(&u) == 0);
  return 0;
}
