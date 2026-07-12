#include <assert.h>

struct S {
  int base;
  int x;
};

extern int m_base(int), m_x(int);
extern int idx_cast(unsigned char *, int), idx_arith(int *, int);
extern int cond_base(int), cond_x(int);
extern struct S cond_ptr(int, struct S *, struct S *);

int
main(void) {
  assert(m_base(5) == 6 && m_x(5) == 7);

  unsigned char buf[4] = {11, 22, 33, 44};
  assert(idx_cast(buf, 2) == 33);
  int arr[4] = {100, 200, 300, 400};
  assert(idx_arith(arr, 2) == 400); /* (arr + 1)[2] == arr[3] */

  assert(cond_base(1) == 10 && cond_base(0) == 30);
  assert(cond_x(1) == 20 && cond_x(0) == 40);

  struct S a = {7, 8}, b = {9, 10};
  struct S r = cond_ptr(1, &a, &b);
  assert(r.base == 7 && r.x == 8);
  r = cond_ptr(0, &a, &b);
  assert(r.base == 9 && r.x == 10);

  return 0;
}
