#include <assert.h>

union U {
  float f;
  int i;
};

struct S {
  union U u;
  int x;
};

union UF {
  float f;
  double d;
};

union U2 {
  long l[2];
  double d;
};

union UB {
  long l[3];
  double d;
};

union U8 {
  long l;
  double d;
};

struct S2 {
  union U8 u;
  int w;
};

struct Pair {
  int a;
  int b;
};

union US {
  struct Pair p;
  double d;
};

extern int getint(union U x);
extern union U mkfloat(float f);
extern int struct_with_union(struct S x);
extern double get_sse_d(union UF x);
extern union UF mk_sse_d(double x);
extern long sum_u2(union U2 x);
extern union U2 mk_u2(long a, long b);
extern long sum_big(union UB x);
extern union UB mk_big(long a, long b, long c);
extern long s2_union_l(struct S2 x);
extern int s2_w(struct S2 x);
extern int us_first(union US x);
extern int us_second(union US x);
extern union US mk_us_pair(int a, int b);
extern double us_as_d(union US x);

int
main() {
  union U u;

  u.i = 42;
  assert(getint(u) == 42);

  u.i = -1;
  assert(getint(u) == -1);

  u = mkfloat(3.14f);
  assert(u.f == 3.14f);

  struct S s;
  s.u.i = 0;
  s.x = 99;
  assert(struct_with_union(s) == 99);

  union UF uf;
  uf.d = 2.5;
  assert(get_sse_d(uf) == 2.5);

  uf = mk_sse_d(-7.25);
  assert(uf.d == -7.25);

  union U2 u2;
  u2.l[0] = 3;
  u2.l[1] = 5;
  assert(sum_u2(u2) == 8);

  u2 = mk_u2(10, 20);
  assert(u2.l[0] == 10);
  assert(u2.l[1] == 20);

  union UB ub;
  ub.l[0] = 1;
  ub.l[1] = 2;
  ub.l[2] = 3;
  assert(sum_big(ub) == 6);

  ub = mk_big(100, 200, 300);
  assert(ub.l[0] == 100);
  assert(ub.l[1] == 200);
  assert(ub.l[2] == 300);

  struct S2 s2;
  s2.u.l = 42;
  s2.w = 77;
  assert(s2_union_l(s2) == 42);
  assert(s2_w(s2) == 77);

  union US us;
  us.p.a = 11;
  us.p.b = 22;
  assert(us_first(us) == 11);
  assert(us_second(us) == 22);

  us = mk_us_pair(33, 44);
  assert(us.p.a == 33);
  assert(us.p.b == 44);

  us.d = 1.5;
  assert(us_as_d(us) == 1.5);
}
