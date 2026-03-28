#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 1);
  assert(foo(0xfffffffe) == 0xfffffffe);
  assert(foo(0xffffffff) == 0);
  assert(foo(999) == (999u % 0xffffffffu));
}
