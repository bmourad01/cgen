#include <assert.h>

struct t {
  long a;
  long b;
  long c;
};

extern struct t mk(long, long, long);
extern long sum(long, long, long);

int
main() {
  struct t s = mk(10, 20, 30);
  assert(s.a == 10);
  assert(s.b == 20);
  assert(s.c == 30);

  assert(sum(10, 20, 30) == 60);
  assert(sum(1, 2, 3) == 6);
  assert(sum(-5, 5, 100) == 100);
}
