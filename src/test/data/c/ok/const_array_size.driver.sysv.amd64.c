#include <assert.h>

extern unsigned long size_sizeof(void), size_arith(void), size_enum(void);
extern int roundtrip(void);

int
main(void) {
  assert(size_sizeof() == 768);
  assert(size_arith() == 56);
  assert(size_enum() == 14);
  assert(roundtrip() == 42);
  return 0;
}
