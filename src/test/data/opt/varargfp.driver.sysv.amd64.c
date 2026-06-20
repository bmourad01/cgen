#include <assert.h>

extern double six(void);

int
main() {
  assert(six() == 6.0);
}
