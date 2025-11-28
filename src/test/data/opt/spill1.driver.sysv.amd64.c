#include <assert.h>

// NB: do not call this with 0
extern int foo(int n);

int
main() {
  assert(foo(1) == 136);
  assert(foo(2) == 272);
  assert(foo(3) == 408);
  assert(foo(4) == 544);
  assert(foo(5) == 680);
  assert(foo(10) == 1360);
  assert(foo(16) == 2176);
  assert(foo(1000) == 136000);
}
