#include <assert.h>

struct flags {
  unsigned ready : 1;
  unsigned mode : 3;
  int sign : 4;
  unsigned wide : 20;
};

extern unsigned get_ready(struct flags *f);
extern unsigned get_mode(struct flags *f);
extern int get_sign(struct flags *f);
extern unsigned get_wide(struct flags *f);
extern void set_mode(struct flags *f, unsigned v);
extern void set_sign(struct flags *f, int v);
extern void set_wide(struct flags *f, unsigned v);
extern int packed_sum(void);
extern unsigned assign_value_unsigned(struct flags *f);
extern int assign_value_signed(struct flags *f);
extern unsigned compound_value(struct flags *f);
extern int signed_compare(struct flags *f);

int
main(void) {
  struct flags f = {0};
  set_mode(&f, 5);
  assert(get_mode(&f) == 5);
  set_sign(&f, -3);
  assert(get_sign(&f) == -3);
  set_wide(&f, 100000);
  assert(get_wide(&f) == 100000);
  assert(get_mode(&f) == 5);
  assert(get_sign(&f) == -3);
  assert(get_ready(&f) == 0);
  set_mode(&f, 13);
  assert(get_mode(&f) == 5);
  set_sign(&f, 13);
  assert(get_sign(&f) == -3);
  assert(packed_sum() == 1003);
  assert(assign_value_unsigned(&f) == 5);
  assert(assign_value_signed(&f) == -3);
  assert(compound_value(&f) == 3);
  assert(signed_compare(&f) == 1);
  return 0;
}
