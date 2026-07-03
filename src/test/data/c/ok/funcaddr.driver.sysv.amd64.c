#include <assert.h>

extern int via_addr(int x);
extern int via_bare(int x);
extern int via_var(int x);

int
main(void) {
  assert(via_addr(41) == 42);
  assert(via_bare(41) == 42);
  assert(via_var(41) == 42);
  return 0;
}
