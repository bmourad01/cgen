#include <assert.h>

struct A {
  char a;
  int b : 4;
  unsigned c : 20;
  short d;
};
struct B {
  int x : 4;
  short y;
  int z : 4;
  char w;
};
struct C {
  char a;
  int : 0;
  char b;
};
struct E {
  long long x : 4;
  char arr[4];
  int y : 8;
};

extern unsigned long size_a(void), size_b(void), size_c(void), size_e(void);
extern int a_a(struct A *), a_b(struct A *), a_d(struct A *);
extern unsigned a_c(struct A *);
extern void set_b(struct A *, int), set_c(struct A *, unsigned);
extern int b_x(struct B *), b_y(struct B *), b_z(struct B *), b_w(struct B *);
extern int c_a(struct C *), c_b(struct C *);
extern int ia_a(void), ia_b(void), ia_d(void), ie_arr(int), ie_y(void);
extern unsigned ia_c(void);
extern long long ie_x(void);

int
main(void) {
  assert(size_a() == sizeof(struct A));
  assert(size_b() == sizeof(struct B));
  assert(size_c() == sizeof(struct C));

  struct A a = {0};
  a.a = 0x7f;
  a.b = -3;
  a.c = 100000;
  a.d = 12345;
  assert(a_a(&a) == 127 && a_b(&a) == -3 && a_c(&a) == 100000 &&
         a_d(&a) == 12345);
  set_b(&a, 2);
  assert(a_b(&a) == 2 && a_a(&a) == 127 && a_c(&a) == 100000 &&
         a_d(&a) == 12345);
  set_c(&a, 7);
  assert(a_c(&a) == 7 && a_b(&a) == 2 && a_a(&a) == 127 && a_d(&a) == 12345);

  struct B b = {0};
  b.x = 5;
  b.y = -200;
  b.z = -1;
  b.w = 99;
  assert(b_x(&b) == 5 && b_y(&b) == -200 && b_z(&b) == -1 && b_w(&b) == 99);

  struct C c = {0};
  c.a = 11;
  c.b = 22;
  assert(c_a(&c) == 11 && c_b(&c) == 22);

  assert(size_e() == sizeof(struct E));

  assert(ia_a() == 127 && ia_b() == -3 && ia_c() == 100000 && ia_d() == 12345);
  assert(ie_x() == 6 && ie_y() == 100);
  assert(ie_arr(0) == 10 && ie_arr(1) == 20 && ie_arr(2) == 30 &&
         ie_arr(3) == 40);
  return 0;
}
