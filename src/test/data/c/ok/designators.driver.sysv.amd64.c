#include <assert.h>

extern int single_chain(void);
extern int merge(void);
extern int continuation(void);
extern int brace_then_reset(void);
extern int array_desig(void);
extern int elem_field(void);
extern int multidim(void);
extern int override(void);
extern int overlay_call(void);
extern int overlay_literal(void);
extern int overlay_global(void);

int
main(void) {
  assert(single_chain() == 50);
  assert(merge() == 129);
  assert(continuation() == 123);
  assert(brace_then_reset() == 129);
  assert(array_desig() == 44);
  assert(elem_field() == 1470);
  assert(multidim() == 530);
  assert(override() == 70);
  assert(overlay_call() == 730);
  assert(overlay_literal() == 130);
  assert(overlay_global() == 4670);
  return 0;
}
