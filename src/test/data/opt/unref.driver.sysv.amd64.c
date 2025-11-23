#include <assert.h>

struct t {
  int a;
  int b;
};

extern int sump(struct t *);
extern struct t mkt(int, int);
extern int sumt(int, int);

int main() {
  struct t t1 = mkt(1, 2);
  struct t t2 = mkt(3, 4);
  struct t t3 = mkt(5, 6);
  struct t t4 = mkt(7, 8);
  struct t t5 = mkt(9, 10);

  assert(t1.a == 1);
  assert(t1.b == 2);
  assert(t2.a == 3);
  assert(t2.b == 4);
  assert(t3.a == 5);
  assert(t3.b == 6);
  assert(t4.a == 7);
  assert(t4.b == 8);
  assert(t5.a == 9);
  assert(t5.b == 10);

  assert(sump(&t1) == 3);
  assert(sump(&t2) == 7);
  assert(sump(&t3) == 11);
  assert(sump(&t4) == 15);
  assert(sump(&t5) == 19);

  assert(sumt(1, 2) == 3);
  assert(sumt(3, 4) == 7);
  assert(sumt(5, 6) == 11);
  assert(sumt(7, 8) == 15);
  assert(sumt(9, 10) == 19);
}
