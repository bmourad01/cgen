#include <assert.h>

extern long sized(int n);

int
main(void) {
  assert(sized(1) == 3255307772660550413L);
  assert(sized(2) == 3255307772660553716L);
  assert(sized(5) == 3255307772660566469L);
  assert(sized(17) == 3255307772660660141L);
  assert(sized(100) == 3255307772663176784L);
  return 0;
}
