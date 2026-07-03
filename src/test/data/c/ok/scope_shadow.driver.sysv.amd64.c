#include <assert.h>

extern int after_block(void);
extern int nested(void);
extern int for_shadow(void);

int
main(void) {
  assert(after_block() == 106);
  assert(nested() == 1);
  assert(for_shadow() == 17);
  return 0;
}
