#include <assert.h>
#include <string.h>

extern int ins_size(void);
extern int ins_field(void);
extern int pool_of(int);
extern const char *whoami(void);

int
main(void) {
  assert(ins_size() == 8);
  assert(ins_field() == 42);
  assert(pool_of(0) == 0);
  assert(pool_of(2) == 2);
  assert(strcmp(whoami(), "whoami") == 0);
  return 0;
}
