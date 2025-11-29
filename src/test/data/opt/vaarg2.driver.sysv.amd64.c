#include <assert.h>

extern long foo(long i, ...);
extern char bar(char b, ...); /* NB: bar actually has no named arguments */

struct t {
  long l1;
  long l2;
};

int
main() {
  struct t s = {10, 32};
  assert(foo(5, s) == 47);
  assert(!bar(0));
  assert(bar(1));
}
