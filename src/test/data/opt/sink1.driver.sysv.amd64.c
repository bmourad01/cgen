#include <assert.h>

extern int foo(int x);

int main() {
  assert(foo(0) == 1);
  assert(foo(1) == 0);
  assert(foo(-1) == 0);
  assert(foo(2) == 0);
  assert(foo(1234) == 0);
  assert(foo(-999) == 0);
}
