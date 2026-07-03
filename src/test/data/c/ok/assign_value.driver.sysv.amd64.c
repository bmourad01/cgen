#include <assert.h>

extern int self_ref(void);
extern int compound_self(void);
extern int incdec(void);
extern int chain(void);
extern int cond_assign(void);

int
main(void) {
  assert(self_ref() == 0);
  assert(compound_self() == 10);
  assert(incdec() == 688);
  assert(chain() == 21);
  assert(cond_assign() == 5);
  return 0;
}
