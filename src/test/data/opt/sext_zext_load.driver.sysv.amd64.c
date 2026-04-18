#include <assert.h>
#include <stdint.h>
#include <string.h>

#define DECL_P(name) extern int64_t name(const void *p)
#define DECL_P_I(name) extern int64_t name(const void *p, int64_t i)

DECL_P(sext_b_l_basic);
DECL_P(sext_h_l_basic);
DECL_P(sext_w_l_basic);
DECL_P(zext_b_l_basic);
DECL_P(zext_h_l_basic);

DECL_P(sext_b_l_add);
DECL_P(sext_h_l_add);
DECL_P(sext_w_l_add);
DECL_P(zext_b_l_add);
DECL_P(zext_h_l_add);

DECL_P_I(sext_b_l_add_mul);
DECL_P_I(sext_h_l_add_mul);
DECL_P_I(sext_w_l_add_mul);
DECL_P_I(zext_b_l_add_mul);
DECL_P_I(zext_h_l_add_mul);

DECL_P_I(sext_b_l_add_mul_disp);
DECL_P_I(sext_h_l_add_mul_disp);
DECL_P_I(sext_w_l_add_mul_disp);
DECL_P_I(zext_b_l_add_mul_disp);
DECL_P_I(zext_h_l_add_mul_disp);

DECL_P_I(sext_b_l_add_mul_disp_neg);
DECL_P_I(sext_h_l_add_mul_disp_neg);
DECL_P_I(sext_w_l_add_mul_disp_neg);
DECL_P_I(zext_b_l_add_mul_disp_neg);
DECL_P_I(zext_h_l_add_mul_disp_neg);

/* Pull a typed value out of a byte buffer without strict-aliasing UB. */
static int8_t
rd_b(const uint8_t *p, size_t off) {
  int8_t v;
  memcpy(&v, p + off, sizeof v);
  return v;
}
static uint8_t
rd_ub(const uint8_t *p, size_t off) {
  uint8_t v;
  memcpy(&v, p + off, sizeof v);
  return v;
}
static int16_t
rd_h(const uint8_t *p, size_t off) {
  int16_t v;
  memcpy(&v, p + off, sizeof v);
  return v;
}
static uint16_t
rd_uh(const uint8_t *p, size_t off) {
  uint16_t v;
  memcpy(&v, p + off, sizeof v);
  return v;
}
static int32_t
rd_w(const uint8_t *p, size_t off) {
  int32_t v;
  memcpy(&v, p + off, sizeof v);
  return v;
}

int
main(void) {
  /* Populate the buffer with a pattern that spans the full byte range
     so every sext sign and every zext bit is exercised. */
  uint8_t buf[256];
  for (size_t k = 0; k < sizeof buf; k++) {
    buf[k] = (uint8_t)(k * 97 + 13);
  }

  /* basic: load from buf[0] */
  assert(sext_b_l_basic(buf) == (int64_t)rd_b(buf, 0));
  assert(zext_b_l_basic(buf) == (int64_t)rd_ub(buf, 0));
  assert(sext_h_l_basic(buf) == (int64_t)rd_h(buf, 0));
  assert(zext_h_l_basic(buf) == (int64_t)rd_uh(buf, 0));
  assert(sext_w_l_basic(buf) == (int64_t)rd_w(buf, 0));

  /* add_disp: load from buf[16] */
  assert(sext_b_l_add(buf) == (int64_t)rd_b(buf, 16));
  assert(zext_b_l_add(buf) == (int64_t)rd_ub(buf, 16));
  assert(sext_h_l_add(buf) == (int64_t)rd_h(buf, 16));
  assert(zext_h_l_add(buf) == (int64_t)rd_uh(buf, 16));
  assert(sext_w_l_add(buf) == (int64_t)rd_w(buf, 16));

  /* add_mul: load from buf[i*4] for i in [0, 60) */
  for (int64_t i = 0; i < 60; i++) {
    size_t off = (size_t)(i * 4);
    assert(sext_b_l_add_mul(buf, i) == (int64_t)rd_b(buf, off));
    assert(zext_b_l_add_mul(buf, i) == (int64_t)rd_ub(buf, off));
    assert(sext_h_l_add_mul(buf, i) == (int64_t)rd_h(buf, off));
    assert(zext_h_l_add_mul(buf, i) == (int64_t)rd_uh(buf, off));
    assert(sext_w_l_add_mul(buf, i) == (int64_t)rd_w(buf, off));
  }

  /* add_mul_disp: load from buf[i*4 + 16] for i in [0, 50) */
  for (int64_t i = 0; i < 50; i++) {
    size_t off = (size_t)(i * 4 + 16);
    assert(sext_b_l_add_mul_disp(buf, i) == (int64_t)rd_b(buf, off));
    assert(zext_b_l_add_mul_disp(buf, i) == (int64_t)rd_ub(buf, off));
    assert(sext_h_l_add_mul_disp(buf, i) == (int64_t)rd_h(buf, off));
    assert(zext_h_l_add_mul_disp(buf, i) == (int64_t)rd_uh(buf, off));
    assert(sext_w_l_add_mul_disp(buf, i) == (int64_t)rd_w(buf, off));
  }

  /* add_mul_disp_neg: load from buf[i*4 - 16] for i in [5, 60) */
  for (int64_t i = 5; i < 60; i++) {
    size_t off = (size_t)(i * 4 - 16);
    assert(sext_b_l_add_mul_disp_neg(buf, i) == (int64_t)rd_b(buf, off));
    assert(zext_b_l_add_mul_disp_neg(buf, i) == (int64_t)rd_ub(buf, off));
    assert(sext_h_l_add_mul_disp_neg(buf, i) == (int64_t)rd_h(buf, off));
    assert(zext_h_l_add_mul_disp_neg(buf, i) == (int64_t)rd_uh(buf, off));
    assert(sext_w_l_add_mul_disp_neg(buf, i) == (int64_t)rd_w(buf, off));
  }
}
