#include <assert.h>

extern int le_f32_rr(float x, float y, int a, int b);
extern int ge_f32_const(float x);
extern long lt_f64_rr(double x, double y, long a, long b);
extern int eq_f64_const(double x, int a);
extern int gt_f32_const_ir(float x, int b);

int
main(void) {
  assert(le_f32_rr(1.0f, 2.0f, 10, 20) == 10);
  assert(le_f32_rr(3.0f, 2.0f, 10, 20) == 20);
  assert(le_f32_rr(2.0f, 2.0f, 10, 20) == 10);
  assert(ge_f32_const(15.0f) == 123);
  assert(ge_f32_const(5.0f) == 456);
  assert(lt_f64_rr(1.0, 2.0, 7L, 8L) == 7L);
  assert(lt_f64_rr(2.0, 1.0, 7L, 8L) == 8L);
  assert(eq_f64_const(2.5, 99) == 99);
  assert(eq_f64_const(2.6, 99) == 42);
  assert(gt_f32_const_ir(1.0f, 50) == 9);
  assert(gt_f32_const_ir(-1.0f, 50) == 50);
  return 0;
}
