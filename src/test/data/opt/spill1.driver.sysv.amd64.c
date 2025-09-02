#include <assert.h>

extern int foo(int n);

int main() {
  assert(foo(1) == 136);
}
