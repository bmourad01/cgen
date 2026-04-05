#include <assert.h>
#include <stdint.h>
#include <string.h>

extern float fadd_f32(float x, float y);
extern double fadd_f64(double x, double y);
extern float fsub_f32(float x, float y);
extern double fsub_f64(double x, double y);
extern float fmul_f32(float x, float y);
extern double fmul_f64(double x, double y);
extern float fdiv_f32(float x, float y);
extern double fdiv_f64(double x, double y);
extern float fneg_f32(float x);
extern double fneg_f64(double x);

extern float fadd_f32_const(float x);
extern double fadd_f64_const(double x);
extern float fsub_f32_const(float x);
extern double fsub_f64_const(double x);
extern float fmul_f32_const(float x);
extern double fmul_f64_const(double x);
extern float fdiv_f32_const(float x);
extern double fdiv_f64_const(double x);
extern float fneg_f32_const(void);
extern double fneg_f64_const(void);
extern float fadd_f32_const_lhs(float x);
extern double fadd_f64_const_lhs(double x);
extern float fsub_f32_const_lhs(float x);
extern double fsub_f64_const_lhs(double x);
extern float fmul_f32_const_lhs(float x);
extern double fmul_f64_const_lhs(double x);
extern float fdiv_f32_const_lhs(float x);
extern double fdiv_f64_const_lhs(double x);

extern int flt_f32(float x, float y);
extern int flt_f64(double x, double y);
extern int fle_f32(float x, float y);
extern int fle_f64(double x, double y);
extern int feq_f32(float x, float y);
extern int feq_f64(double x, double y);
extern int fne_f32(float x, float y);
extern int fne_f64(double x, double y);
extern int fuo_f32(float x, float y);
extern int fo_f64(double x, double y);

extern int flt_f32_const(float x);
extern int flt_f64_const(double x);
extern int feq_f32_const(float x);
extern int feq_f64_const(double x);
extern int flt_f32_const_lhs(float x);
extern int flt_f64_const_lhs(double x);
extern int feq_f32_const_lhs(float x);
extern int feq_f64_const_lhs(double x);

extern int br_flt_f32(float x, float y);
extern int br_flt_f64(double x, double y);
extern int br_flt_f32_const(float x);
extern int br_flt_f64_const(double x);
extern int br_flt_f32_const_lhs(float x);
extern int br_flt_f64_const_lhs(double x);

extern signed char ftosi_f32_i8(float x);
extern short ftosi_f32_i16(float x);
extern int ftosi_f32_i32(float x);
extern long ftosi_f32_i64(float x);
extern signed char ftosi_f64_i8(double x);
extern short ftosi_f64_i16(double x);
extern int ftosi_f64_i32(double x);
extern long ftosi_f64_i64(double x);
extern unsigned char ftoui_f32_i8(float x);
extern unsigned short ftoui_f32_i16(float x);
extern unsigned int ftoui_f32_i32(float x);
extern unsigned long ftoui_f32_i64(float x);
extern unsigned char ftoui_f64_i8(double x);
extern unsigned short ftoui_f64_i16(double x);
extern unsigned int ftoui_f64_i32(double x);
extern unsigned long ftoui_f64_i64(double x);
extern float sitof_i8_f32(signed char x);
extern double sitof_i8_f64(signed char x);
extern float sitof_i16_f32(short x);
extern double sitof_i16_f64(short x);
extern float sitof_i32_f32(int x);
extern double sitof_i32_f64(int x);
extern float sitof_i64_f32(long x);
extern double sitof_i64_f64(long x);
extern float uitof_i8_f32(unsigned char x);
extern double uitof_i8_f64(unsigned char x);
extern float uitof_i16_f32(unsigned short x);
extern double uitof_i16_f64(unsigned short x);
extern float uitof_i32_f32(unsigned int x);
extern double uitof_i32_f64(unsigned int x);
extern float uitof_i64_f32(unsigned long x);
extern double uitof_i64_f64(unsigned long x);
extern double fext_f32_f64(float x);
extern float ftrunc_f64_f32(double x);

extern float sel_f32(float x, float y, float yes, float no);
extern double sel_f64(double x, double y, double yes, double no);
extern float sel_f32_const_cmp(float x, float yes, float no);
extern float sel_f32_const_cmp_lhs(float x, float yes, float no);
extern double sel_f64_const_val(double x, double y, double yes);
extern double sel_f64_const_cmp_lhs(double x, double yes, double no);

extern unsigned int ifbits_f32(float x);
extern unsigned long ifbits_f64(double x);
extern float fibits_f32(unsigned int x);
extern double fibits_f64(unsigned long x);

int
main(void) {
  assert(fadd_f32(1.0f, 2.0f) == 3.0f);
  assert(fadd_f64(1.0, 2.0) == 3.0);
  assert(fsub_f32(5.0f, 3.0f) == 2.0f);
  assert(fsub_f64(5.0, 3.0) == 2.0);
  assert(fmul_f32(3.0f, 4.0f) == 12.0f);
  assert(fmul_f64(3.0, 4.0) == 12.0);
  assert(fdiv_f32(10.0f, 4.0f) == 2.5f);
  assert(fdiv_f64(10.0, 4.0) == 2.5);
  assert(fneg_f32(3.0f) == -3.0f);
  assert(fneg_f64(3.0) == -3.0);

  assert(fadd_f32_const(1.0f) == 2.5f);
  assert(fadd_f64_const(1.0) == 2.5);
  assert(fsub_f32_const(5.0f) == 3.5f);
  assert(fsub_f64_const(5.0) == 3.5);
  assert(fmul_f32_const(3.0f) == 6.0f);
  assert(fmul_f64_const(3.0) == 6.0);
  assert(fdiv_f32_const(10.0f) == 5.0f);
  assert(fdiv_f64_const(10.0) == 5.0);
  assert(fneg_f32_const() == -1.5f);
  assert(fneg_f64_const() == -1.5);

  assert(fadd_f32_const_lhs(1.0f) == 2.5f);
  assert(fadd_f64_const_lhs(1.0) == 2.5);
  assert(fsub_f32_const_lhs(0.5f) == 1.0f);
  assert(fsub_f64_const_lhs(0.5) == 1.0);
  assert(fmul_f32_const_lhs(3.0f) == 6.0f);
  assert(fmul_f64_const_lhs(3.0) == 6.0);
  assert(fdiv_f32_const_lhs(4.0f) == 0.5f);
  assert(fdiv_f64_const_lhs(4.0) == 0.5);

  assert(flt_f32(1.0f, 2.0f) == 1);
  assert(flt_f32(2.0f, 1.0f) == 0);
  assert(flt_f64(1.0, 2.0) == 1);
  assert(flt_f64(2.0, 1.0) == 0);
  assert(fle_f32(1.0f, 1.0f) == 1);
  assert(fle_f32(2.0f, 1.0f) == 0);
  assert(fle_f64(1.0, 1.0) == 1);
  assert(fle_f64(2.0, 1.0) == 0);
  assert(feq_f32(1.0f, 1.0f) == 1);
  assert(feq_f32(1.0f, 2.0f) == 0);
  assert(feq_f64(1.0, 1.0) == 1);
  assert(feq_f64(1.0, 2.0) == 0);
  assert(fne_f32(1.0f, 2.0f) == 1);
  assert(fne_f32(1.0f, 1.0f) == 0);
  assert(fne_f64(1.0, 2.0) == 1);
  assert(fne_f64(1.0, 1.0) == 0);
  assert(fuo_f32(0.0f / 0.0f, 1.0f) == 1);
  assert(fuo_f32(1.0f, 1.0f) == 0);
  assert(fo_f64(1.0, 2.0) == 1);
  assert(fo_f64(0.0 / 0.0, 1.0) == 0);

  assert(flt_f32_const(-1.0f) == 1);
  assert(flt_f32_const(1.0f) == 0);
  assert(flt_f64_const(-1.0) == 1);
  assert(flt_f64_const(1.0) == 0);
  assert(feq_f32_const(1.0f) == 1);
  assert(feq_f32_const(2.0f) == 0);
  assert(feq_f64_const(1.0) == 1);
  assert(feq_f64_const(2.0) == 0);

  assert(flt_f32_const_lhs(1.0f) == 1);  /* 0.0 < 1.0 */
  assert(flt_f32_const_lhs(-1.0f) == 0); /* 0.0 < -1.0 */
  assert(flt_f64_const_lhs(1.0) == 1);
  assert(flt_f64_const_lhs(-1.0) == 0);
  assert(feq_f32_const_lhs(1.0f) == 1); /* 1.0 == 1.0 */
  assert(feq_f32_const_lhs(2.0f) == 0);
  assert(feq_f64_const_lhs(1.0) == 1);
  assert(feq_f64_const_lhs(2.0) == 0);

  assert(br_flt_f32(1.0f, 2.0f) == 1);
  assert(br_flt_f32(2.0f, 1.0f) == 0);
  assert(br_flt_f64(1.0, 2.0) == 1);
  assert(br_flt_f64(2.0, 1.0) == 0);
  assert(br_flt_f32_const(-1.0f) == 1);
  assert(br_flt_f32_const(1.0f) == 0);
  assert(br_flt_f64_const(-1.0) == 1);
  assert(br_flt_f64_const(1.0) == 0);
  assert(br_flt_f32_const_lhs(1.0f) == 1);  /* 0.0 < 1.0 */
  assert(br_flt_f32_const_lhs(-1.0f) == 0); /* 0.0 < -1.0 */
  assert(br_flt_f64_const_lhs(1.0) == 1);
  assert(br_flt_f64_const_lhs(-1.0) == 0);

  assert(ftosi_f32_i8(3.7f) == 3);
  assert(ftosi_f32_i8(-3.7f) == -3);
  assert(ftosi_f32_i16(3.7f) == 3);
  assert(ftosi_f32_i16(-3.7f) == -3);
  assert(ftosi_f32_i32(3.7f) == 3);
  assert(ftosi_f32_i32(-3.7f) == -3);
  assert(ftosi_f32_i64(3.7f) == 3L);
  assert(ftosi_f32_i64(-3.7f) == -3L);
  assert(ftosi_f64_i8(3.7) == 3);
  assert(ftosi_f64_i8(-3.7) == -3);
  assert(ftosi_f64_i16(3.7) == 3);
  assert(ftosi_f64_i16(-3.7) == -3);
  assert(ftosi_f64_i32(3.7) == 3);
  assert(ftosi_f64_i32(-3.7) == -3);
  assert(ftosi_f64_i64(3.7) == 3L);
  assert(ftosi_f64_i64(-3.7) == -3L);

  assert(ftoui_f32_i8(3.7f) == 3u);
  assert(ftoui_f32_i8(0.0f) == 0u);
  assert(ftoui_f32_i16(3.7f) == 3u);
  assert(ftoui_f32_i16(0.0f) == 0u);
  assert(ftoui_f32_i32(3.7f) == 3u);
  assert(ftoui_f32_i32(0.0f) == 0u);
  assert(ftoui_f32_i64(3.7f) == 3UL);
  assert(ftoui_f32_i64(0.0f) == 0UL);
  assert(ftoui_f32_i64(9.223372036854776e18f) == 9223372036854775808UL);
  assert(ftoui_f64_i8(3.7) == 3u);
  assert(ftoui_f64_i8(0.0) == 0u);
  assert(ftoui_f64_i16(3.7) == 3u);
  assert(ftoui_f64_i16(0.0) == 0u);
  assert(ftoui_f64_i32(3.7) == 3u);
  assert(ftoui_f64_i32(0.0) == 0u);
  assert(ftoui_f64_i64(3.7) == 3UL);
  assert(ftoui_f64_i64(0.0) == 0UL);
  assert(ftoui_f64_i64(9.223372036854776e18) == 9223372036854775808UL);

  assert(sitof_i8_f32(5) == 5.0f);
  assert(sitof_i8_f32(-3) == -3.0f);
  assert(sitof_i8_f64(5) == 5.0);
  assert(sitof_i8_f64(-3) == -3.0);
  assert(sitof_i16_f32(5) == 5.0f);
  assert(sitof_i16_f32(-3) == -3.0f);
  assert(sitof_i16_f64(5) == 5.0);
  assert(sitof_i16_f64(-3) == -3.0);
  assert(sitof_i32_f32(5) == 5.0f);
  assert(sitof_i32_f32(-3) == -3.0f);
  assert(sitof_i32_f64(5) == 5.0);
  assert(sitof_i32_f64(-3) == -3.0);
  assert(sitof_i64_f32(100L) == 100.0f);
  assert(sitof_i64_f32(-1L) == -1.0f);
  assert(sitof_i64_f64(100L) == 100.0);
  assert(sitof_i64_f64(-1L) == -1.0);

  assert(uitof_i8_f32(200u) == 200.0f);
  assert(uitof_i8_f32(0u) == 0.0f);
  assert(uitof_i8_f64(200u) == 200.0);
  assert(uitof_i8_f64(0u) == 0.0);
  assert(uitof_i16_f32(60000u) == 60000.0f);
  assert(uitof_i16_f32(0u) == 0.0f);
  assert(uitof_i16_f64(60000u) == 60000.0);
  assert(uitof_i16_f64(0u) == 0.0);
  assert(uitof_i32_f32(5u) == 5.0f);
  assert(uitof_i32_f32(0u) == 0.0f);
  assert(uitof_i32_f32(2147483648u) == 2147483648.0f);
  assert(uitof_i32_f64(5u) == 5.0);
  assert(uitof_i32_f64(0u) == 0.0);
  assert(uitof_i32_f64(2147483648u) == 2147483648.0);
  assert(uitof_i64_f32(0UL) == 0.0f);
  assert(uitof_i64_f32(9223372036854775808UL) == 9223372036854775808.0f);
  assert(uitof_i64_f64(0UL) == 0.0);
  assert(uitof_i64_f64(9223372036854775808UL) == 9.223372036854776e18);

  assert(fext_f32_f64(1.5f) == 1.5);
  assert(ftrunc_f64_f32(1.5) == 1.5f);

  assert(sel_f32(1.0f, 2.0f, 10.0f, 20.0f) == 10.0f);
  assert(sel_f32(2.0f, 1.0f, 10.0f, 20.0f) == 20.0f);
  assert(sel_f64(1.0, 2.0, 10.0, 20.0) == 10.0);
  assert(sel_f64(2.0, 1.0, 10.0, 20.0) == 20.0);
  assert(sel_f32_const_cmp(-1.0f, 10.0f, 20.0f) == 10.0f);
  assert(sel_f32_const_cmp(1.0f, 10.0f, 20.0f) == 20.0f);
  assert(sel_f32_const_cmp_lhs(1.0f, 10.0f, 20.0f) == 10.0f);  /* 0.0 < 1.0 */
  assert(sel_f32_const_cmp_lhs(-1.0f, 10.0f, 20.0f) == 20.0f); /* 0.0 < -1.0 */
  assert(sel_f64_const_val(1.0, 2.0, 5.0) == 5.0);
  assert(sel_f64_const_val(2.0, 1.0, 5.0) == 0.0);
  assert(sel_f64_const_cmp_lhs(1.0, 10.0, 20.0) == 10.0);  /* 0.0 < 1.0 */
  assert(sel_f64_const_cmp_lhs(-1.0, 10.0, 20.0) == 20.0); /* 0.0 < -1.0 */

  assert(ifbits_f32(1.0f) == 0x3f800000u);
  assert(ifbits_f64(1.0) == 0x3ff0000000000000UL);
  assert(fibits_f32(0x3f800000u) == 1.0f);
  assert(fibits_f64(0x3ff0000000000000UL) == 1.0);
}
