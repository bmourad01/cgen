#include <assert.h>

extern int sep_init(void);
extern int sep_write(int x, int y);
extern int lead_init(void);
extern unsigned long sep_size(void);
extern unsigned long lead_size(void);

int
main(void) {
  assert(sep_init() == 12);
  assert(sep_write(7, 3) == 73);
  assert(sep_write(7, -3) == 67);
  assert(lead_init() == 9);
  assert(sep_size() == 8);
  assert(lead_size() == 4);
  return 0;
}
