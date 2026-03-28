#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 0);
  assert(foo(0xfffffffe) == 0);
  assert(foo(0xffffffff) == 1);
}
