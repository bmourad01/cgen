#include <assert.h>

struct __attribute__((packed)) Packed {
  char c;
  int i;
};
struct __attribute__((aligned(16))) Over {
  int x;
};

extern unsigned long packed_size(void), over_size(void), over_align(void),
  member_offset(void), alignof_double(void);
extern int alignof_expr(void), local_aligned(void);

int
main(void) {
  assert(packed_size() == sizeof(struct Packed) && packed_size() == 5);
  assert(over_size() == sizeof(struct Over) && over_size() == 16);
  assert(over_align() == _Alignof(struct Over) && over_align() == 16);
  assert(member_offset() == 8);
  assert(alignof_double() == _Alignof(double) && alignof_double() == 8);
  assert(alignof_expr() == __alignof__(long) && alignof_expr() == 8);
  assert(local_aligned() == 1);
  return 0;
}
