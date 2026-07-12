#include <assert.h>

extern int enum_consts(void), anon_struct(void), named_struct(void),
  anon_union(void), sibling_scopes(void);

int
main(void) {
  assert(enum_consts() == 14);
  assert(anon_struct() == 34);
  assert(named_struct() == 11);
  assert(anon_union() == 0xbeef);
  assert(sibling_scopes() == 30);
  return 0;
}
