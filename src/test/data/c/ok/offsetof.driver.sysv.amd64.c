#include <assert.h>
#include <stddef.h>

struct S {
  char a;
  int b;
  char c;
  long d;
  int e[4];
};

struct Nest {
  int pad;
  struct S inner;
};

extern unsigned long off_b(void), off_d(void), off_e2(void), off_nested(void);
extern unsigned long tab(int), sized_len(void), local_len(void);

int
main(void) {
  assert(off_b() == offsetof(struct S, b));
  assert(off_d() == offsetof(struct S, d));
  assert(off_e2() == offsetof(struct S, e[2]));
  assert(off_nested() == offsetof(struct Nest, inner.d));
  assert(tab(0) == 0);
  assert(tab(1) == offsetof(struct S, b));
  assert(tab(2) == offsetof(struct S, d));
  assert(sized_len() == offsetof(struct S, d));
  assert(local_len() == offsetof(struct S, d));
  return 0;
}
