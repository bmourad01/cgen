#include <assert.h>
#include <stdint.h>

extern int sge_branch(long x);
extern int sgt_branch(long x);
extern int sle_branch(long x);
extern int slt_branch(long x);
extern int eq_branch(long x);
extern int ne_branch(long x);

extern int sge_flag(long x);
extern int eq_flag(long x);

extern long sel_sge(long x, long yes, long no);

extern long mul_boundary(long x);

extern long add_ptr_hi(long base);
extern long sub_ptr_hi(long base);
extern long add_ptr_max32(long base);

extern int test_branch(long x);
extern int test_flag(long x);

extern long or_hi(long x);
extern long xor_hi(long x);
extern long and_hi(long x);

extern long load_with_disp(long base);
extern void store_with_disp(long val, long base);

int
main() {
  assert(sge_branch(0) == 0);
  assert(sge_branch(2147483647L) == 0);
  assert(sge_branch(2147483648L) == 1);
  assert(sge_branch(4294967295L) == 1);
  assert(sge_branch(-1L) == 0);

  assert(sgt_branch(0) == 0);
  assert(sgt_branch(2147483648L) == 0);
  assert(sgt_branch(2147483649L) == 1);
  assert(sgt_branch(-1L) == 0);

  assert(sle_branch(0) == 1);
  assert(sle_branch(2147483648L) == 1);
  assert(sle_branch(2147483649L) == 0);
  assert(sle_branch(-1L) == 1);

  assert(slt_branch(0) == 1);
  assert(slt_branch(2147483647L) == 1);
  assert(slt_branch(2147483648L) == 0);
  assert(slt_branch(-1L) == 1);

  assert(eq_branch(0) == 0);
  assert(eq_branch(2147483648L) == 1);
  assert(eq_branch(-2147483648L) == 0);

  assert(ne_branch(0) == 1);
  assert(ne_branch(2147483648L) == 0);
  assert(ne_branch(-2147483648L) == 1);

  assert(sge_flag(0) == 0);
  assert(sge_flag(2147483647L) == 0);
  assert(sge_flag(2147483648L) == 1);
  assert(sge_flag(-1L) == 0);

  assert(eq_flag(0) == 0);
  assert(eq_flag(2147483648L) == 1);
  assert(eq_flag(-2147483648L) == 0);

  assert(sel_sge(0, 10L, 20L) == 20L);
  assert(sel_sge(2147483648L, 10L, 20L) == 10L);
  assert(sel_sge(-1L, 10L, 20L) == 20L);

  assert(mul_boundary(0) == 0);
  assert(mul_boundary(1) == 2147483648L);
  assert(mul_boundary(2) == 4294967296L);
  assert(mul_boundary(-1) == -2147483648L);

  assert(add_ptr_hi(0) == 2147483648L);
  assert(add_ptr_hi(1) == 2147483649L);
  assert(add_ptr_hi(-1L) == 2147483647L);

  assert(sub_ptr_hi(0) == -2147483649L);
  assert(sub_ptr_hi(2147483649L) == 0);

  assert(add_ptr_max32(0) == 2147483647L);
  assert(add_ptr_max32(1) == 2147483648L);

  assert(test_branch(0) == 0);
  assert(test_branch(2147483648L) == 1);
  assert(test_branch(2147483647L) == 0);
  assert(test_branch(-1L) == 1);

  assert(test_flag(0) == 0);
  assert(test_flag(2147483648L) == 1);
  assert(test_flag(2147483647L) == 0);
  assert(test_flag(-1L) == 1);

  assert(or_hi(0) == 2147483648L);
  assert(or_hi(1) == 2147483649L);
  assert(or_hi(2147483648L) == 2147483648L);

  assert(xor_hi(0) == 2147483648L);
  assert(xor_hi(2147483648L) == 0);
  assert(xor_hi(-1L) == ~2147483648L);

  assert(and_hi(0) == 0);
  assert(and_hi(2147483648L) == 2147483648L);
  assert(and_hi(-1L) == 2147483648L);

  long arr[2] = {0, 0};
  store_with_disp(42L, (long)arr);
  assert(arr[1] == 42L);
  assert(load_with_disp((long)arr) == 42L);
}
