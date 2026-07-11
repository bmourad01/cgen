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
struct P {
  unsigned lo : 3;
  int mid : 30;
  unsigned hi : 13;
  char tail;
} __attribute__((packed));

extern unsigned long size_a(void), size_b(void), size_c(void), size_e(void);
extern unsigned long size_p(void);
extern int a_a(struct A *), a_b(struct A *), a_d(struct A *);
extern unsigned a_c(struct A *);
extern void set_b(struct A *, int), set_c(struct A *, unsigned);
extern int b_x(struct B *), b_y(struct B *), b_z(struct B *), b_w(struct B *);
extern int c_a(struct C *), c_b(struct C *);
extern int ia_a(void), ia_b(void), ia_d(void), ie_arr(int), ie_y(void);
extern unsigned ia_c(void);
extern long long ie_x(void);
extern unsigned p_lo(struct P *), p_hi(struct P *);
extern int p_mid(struct P *), p_tail(struct P *);
extern void set_mid(struct P *, int), set_hi(struct P *, unsigned);
extern int ip_mid(void);
extern unsigned ip_hi(void);

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

  assert(size_p() == sizeof(struct P));

  struct P p = {0};
  p.tail = 0x5a;
  p.lo = 5;
  p.mid = -1000000; /* straddles the 4-byte unit; byte-wise access */
  p.hi = 5000;
  assert(p_lo(&p) == 5 && p_mid(&p) == -1000000 && p_hi(&p) == 5000 &&
         p_tail(&p) == 0x5a);
  set_mid(&p, 123456789);
  assert(p_mid(&p) == 123456789 && p_lo(&p) == 5 && p_hi(&p) == 5000 &&
         p_tail(&p) == 0x5a);
  set_mid(&p, -1); /* sign extension across the byte-wise read */
  assert(p_mid(&p) == -1 && p_lo(&p) == 5 && p_hi(&p) == 5000);
  set_hi(&p, 0x1fff);
  assert(p_hi(&p) == 0x1fff && p_mid(&p) == -1 && p_lo(&p) == 5 &&
         p_tail(&p) == 0x5a);

  assert(ip_mid() == -1000000 && ip_hi() == 5000);
  return 0;
}
