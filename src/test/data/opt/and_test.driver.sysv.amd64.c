#include <assert.h>

extern int foo(int x, int y);
extern int bar(int x, int y);
extern long baz(long x);

int main() {
  assert(foo(3, 4) == 3);
  assert(foo(4, 4) == 4);
  assert(foo(1, 4) == 1);

  assert(bar(3, 4) == 4);
  assert(bar(4, 4) == 5);
  assert(bar(1, 4) == 2);

  assert(baz(0) == 1);
  assert(baz(1) == 3);
  assert(baz(2) == 5);
  assert(baz(3) == 7);
  assert(baz(4) == 5);
}
