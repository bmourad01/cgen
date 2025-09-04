#include <assert.h>

struct S {
  double d;
  long l;
};

extern long foo(long i, ...);

int main() {
  struct S s = {0.0, 1};
  assert(foo(1, s) == 3);
}
