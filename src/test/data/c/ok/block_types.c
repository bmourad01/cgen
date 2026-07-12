/* Block-scope type declarations (§6.2.1, §6.7.2.3, §6.7.8) */

struct Shadowed {
  int outer;
};

int
enum_consts(void) {
  enum { A = 1, B = 2, C = 4, D = A | B | C };
  return A + B + C + D;
}

int
anon_struct(void) {
  struct {
    int a;
    int b;
  } x = {3, 4};
  return x.a * 10 + x.b;
}

int
named_struct(void) {
  struct P {
    int x, y;
  } p = {5, 6};
  struct P q = p;
  return q.x + q.y;
}

int
anon_union(void) {
  union {
    int i;
    unsigned char b[4];
  } u;
  u.i = 0;
  u.b[0] = 0xef;
  u.b[1] = 0xbe;
  return u.i & 0xffff;
}

int
sibling_scopes(void) {
  int r = 0;
  {
    enum { X = 10 };
    r += X;
  }
  {
    enum { X = 20 };
    r += X;
  }
  return r;
}

int
block_typedef(void) {
  typedef int myint;
  myint y = 3;
  typedef struct {
    int a, b;
  } pair;
  pair p = {4, 5};
  return y + p.a + p.b;
}

int
sibling_typedef_a(void) {
  typedef int T;
  T x = 5;
  return x;
}

long
sibling_typedef_b(void) {
  typedef long T;
  T x = 7;
  return x;
}

int
nested_redecl(void) {
  typedef int T;
  T a = 1;
  {
    typedef int T;
    T b = 2;
    return a + b;
  }
}

int
shadow_struct(void) {
  struct Shadowed a = {.outer = 7};
  struct Shadowed {
    long inner;
  } b = {.inner = 8};
  return a.outer + (int)b.inner;
}

int
sibling_tags(void) {
  int r = 0;
  {
    struct T {
      int a;
    } x = {.a = 3};
    r += x.a;
  }
  {
    struct T {
      long b, c;
    } x = {.b = 4, .c = 5};
    r += (int)(x.b + x.c);
  }
  return r;
}
