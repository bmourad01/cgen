#include <assert.h>

extern int get_int(void);
extern long get_long(void);
extern char get_msg(int i);
extern int get_arr(int i);
extern int get_sparse(int i);
extern char get_name(int i);
extern char get_exact(int i);
extern char get_flex(int i);
extern char get_empty(int i);
extern int pt_x(void);
extern int pt_y(void);
extern int pad_c(void);
extern int pad_n(void);
extern int pts_sum(void);
extern int deref_pelem(void);
extern int deref_pmemb(void);
extern int pnull_null(void);
extern int deref_pconst(void);
extern int deref_pcelem(void);
extern int pcarr_get(int i);

int
main(void) {
  assert(get_int() == 42);
  assert(get_long() == 1234567);
  assert(get_msg(0) == 'h');
  assert(get_msg(4) == 'o');
  assert(get_arr(0) == 10);
  assert(get_arr(1) == 20);
  assert(get_arr(2) == 30);
  assert(get_arr(3) == 40);
  assert(get_sparse(0) == 1);
  assert(get_sparse(1) == 2);
  assert(get_sparse(2) == 0);
  assert(get_sparse(4) == 0);
  assert(get_name(0) == 'a');
  assert(get_name(1) == 'b');
  assert(get_name(2) == 'c');
  assert(get_name(3) == 0);
  assert(get_exact(0) == 'a');
  assert(get_exact(1) == 'b');
  assert(get_exact(2) == 'c');
  assert(get_flex(0) == 'a');
  assert(get_flex(1) == 'b');
  assert(get_flex(2) == 'c');
  assert(get_flex(3) == 0);
  assert(get_empty(0) == 0);
  assert(get_empty(1) == 0);
  assert(get_empty(2) == 0);
  assert(get_empty(3) == 0);
  assert(pt_x() == 3);
  assert(pt_y() == 4);
  assert(pad_c() == 7);
  assert(pad_n() == 100);
  assert(pts_sum() == 10);
  assert(deref_pelem() == 30);
  assert(deref_pmemb() == 4);
  assert(pnull_null() == 1);
  assert(deref_pconst() == 42);
  assert(deref_pcelem() == 20);
  assert(pcarr_get(0) == 42);
  assert(pcarr_get(1) == -1);
  assert(pcarr_get(2) == 40);
  return 0;
}
