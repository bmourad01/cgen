#include <assert.h>

extern int plain(int);
extern int in_branch(int);
extern long keeps_type(long);
extern int nested(int, int);
extern int const_hint(int);

int
main(void) {
  assert(plain(5) == 5);
  assert(plain(0) == 0);
  assert(plain(-7) == -7);
  assert(in_branch(3) == 1);
  assert(in_branch(-2) == 0);
  assert(keeps_type(41) == 42);
  assert(nested(2, 3) == 5);
  assert(const_hint(9) == 9);
  return 0;
}
