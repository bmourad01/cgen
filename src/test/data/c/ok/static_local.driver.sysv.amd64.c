#include <assert.h>

extern int next_id(void);
extern int next_seq(void);
extern char greeting_char(int i);
extern int squares(int n);
extern int get_shared(void);

int
main(void) {
  assert(next_id() == 1);
  assert(next_id() == 2);
  assert(next_id() == 3);
  assert(next_seq() == 101);
  assert(next_seq() == 102);
  assert(next_id() == 4);
  assert(greeting_char(0) == 'h');
  assert(greeting_char(1) == 'i');
  assert(greeting_char(2) == 0);
  assert(squares(3) == 33);
  assert(get_shared() == 7);
  return 0;
}
