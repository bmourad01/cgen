#include <assert.h>
#include <stdint.h>
#include <string.h>

#define DECL_LOAD_P(ret, name) extern ret name(const void *p)
#define DECL_LOAD_P_I(ret, name) extern ret name(const void *p, int64_t i)
#define DECL_STORE_P(name, val) extern void name(void *p, val v)
#define DECL_STORE_P_I(name, val) extern void name(void *p, int64_t i, val v)

DECL_LOAD_P(int8_t, load_b_basic);
DECL_LOAD_P(int16_t, load_h_basic);
DECL_LOAD_P(int32_t, load_w_basic);
DECL_LOAD_P(int64_t, load_l_basic);

DECL_STORE_P(store_b_basic, int8_t);
DECL_STORE_P(store_h_basic, int16_t);
DECL_STORE_P(store_w_basic, int32_t);
DECL_STORE_P(store_l_basic, int64_t);

DECL_LOAD_P(int8_t, load_b_add);
DECL_LOAD_P(int16_t, load_h_add);
DECL_LOAD_P(int32_t, load_w_add);
DECL_LOAD_P(int64_t, load_l_add);

DECL_STORE_P(store_b_add, int8_t);
DECL_STORE_P(store_h_add, int16_t);
DECL_STORE_P(store_w_add, int32_t);
DECL_STORE_P(store_l_add, int64_t);

DECL_LOAD_P_I(int8_t, load_b_add_mul);
DECL_LOAD_P_I(int16_t, load_h_add_mul);
DECL_LOAD_P_I(int32_t, load_w_add_mul);
DECL_LOAD_P_I(int64_t, load_l_add_mul);

DECL_STORE_P_I(store_b_add_mul, int8_t);
DECL_STORE_P_I(store_h_add_mul, int16_t);
DECL_STORE_P_I(store_w_add_mul, int32_t);
DECL_STORE_P_I(store_l_add_mul, int64_t);

DECL_LOAD_P_I(int8_t, load_b_add_mul_disp);
DECL_LOAD_P_I(int16_t, load_h_add_mul_disp);
DECL_LOAD_P_I(int32_t, load_w_add_mul_disp);
DECL_LOAD_P_I(int64_t, load_l_add_mul_disp);

DECL_STORE_P_I(store_b_add_mul_disp, int8_t);
DECL_STORE_P_I(store_h_add_mul_disp, int16_t);
DECL_STORE_P_I(store_w_add_mul_disp, int32_t);
DECL_STORE_P_I(store_l_add_mul_disp, int64_t);

DECL_LOAD_P_I(int8_t, load_b_add_mul_disp_neg);
DECL_LOAD_P_I(int16_t, load_h_add_mul_disp_neg);
DECL_LOAD_P_I(int32_t, load_w_add_mul_disp_neg);
DECL_LOAD_P_I(int64_t, load_l_add_mul_disp_neg);

DECL_STORE_P_I(store_b_add_mul_disp_neg, int8_t);
DECL_STORE_P_I(store_h_add_mul_disp_neg, int16_t);
DECL_STORE_P_I(store_w_add_mul_disp_neg, int32_t);
DECL_STORE_P_I(store_l_add_mul_disp_neg, int64_t);

/* memcpy-based typed reads to avoid strict-aliasing UB. */
#define RD(T, name)                                                            \
  static T name(const uint8_t *p, size_t off) {                                \
    T v;                                                                       \
    memcpy(&v, p + off, sizeof v);                                             \
    return v;                                                                  \
  }
RD(int8_t, rd_b)
RD(int16_t, rd_h)
RD(int32_t, rd_w)
RD(int64_t, rd_l)
#undef RD

static void
fill(uint8_t *buf, size_t n) {
  for (size_t k = 0; k < n; k++) {
    buf[k] = (uint8_t)(k * 97 + 13);
  }
}

int
main(void) {
  uint8_t buf[256];
  uint8_t scratch[256];

  /* basic loads: read from buf[0] */
  fill(buf, sizeof buf);
  assert(load_b_basic(buf) == rd_b(buf, 0));
  assert(load_h_basic(buf) == rd_h(buf, 0));
  assert(load_w_basic(buf) == rd_w(buf, 0));
  assert(load_l_basic(buf) == rd_l(buf, 0));

  /* basic stores: write to scratch[0] */
  fill(scratch, sizeof scratch);
  store_b_basic(scratch, (int8_t)0x5A);
  assert(rd_b(scratch, 0) == (int8_t)0x5A);
  fill(scratch, sizeof scratch);
  store_h_basic(scratch, (int16_t)0x1234);
  assert(rd_h(scratch, 0) == (int16_t)0x1234);
  fill(scratch, sizeof scratch);
  store_w_basic(scratch, (int32_t)0xDEADBEEF);
  assert(rd_w(scratch, 0) == (int32_t)0xDEADBEEF);
  fill(scratch, sizeof scratch);
  store_l_basic(scratch, (int64_t)0xCAFEF00DDEADBEEFLL);
  assert(rd_l(scratch, 0) == (int64_t)0xCAFEF00DDEADBEEFLL);

  /* add (base+disp): offset 16 */
  assert(load_b_add(buf) == rd_b(buf, 16));
  assert(load_h_add(buf) == rd_h(buf, 16));
  assert(load_w_add(buf) == rd_w(buf, 16));
  assert(load_l_add(buf) == rd_l(buf, 16));

  fill(scratch, sizeof scratch);
  store_b_add(scratch, (int8_t)0x7E);
  assert(rd_b(scratch, 16) == (int8_t)0x7E);
  fill(scratch, sizeof scratch);
  store_h_add(scratch, (int16_t)0x4321);
  assert(rd_h(scratch, 16) == (int16_t)0x4321);
  fill(scratch, sizeof scratch);
  store_w_add(scratch, (int32_t)0x12345678);
  assert(rd_w(scratch, 16) == (int32_t)0x12345678);
  fill(scratch, sizeof scratch);
  store_l_add(scratch, (int64_t)0x0123456789ABCDEFLL);
  assert(rd_l(scratch, 16) == (int64_t)0x0123456789ABCDEFLL);

  /* add_mul: offset i*4 */
  for (int64_t i = 0; i < 60; i++) {
    size_t off = (size_t)(i * 4);
    assert(load_b_add_mul(buf, i) == rd_b(buf, off));
    assert(load_h_add_mul(buf, i) == rd_h(buf, off));
    assert(load_w_add_mul(buf, i) == rd_w(buf, off));
    assert(load_l_add_mul(buf, i) == rd_l(buf, off));

    fill(scratch, sizeof scratch);
    store_b_add_mul(scratch, i, (int8_t)(i + 1));
    assert(rd_b(scratch, off) == (int8_t)(i + 1));
    fill(scratch, sizeof scratch);
    store_h_add_mul(scratch, i, (int16_t)(i * 131 + 7));
    assert(rd_h(scratch, off) == (int16_t)(i * 131 + 7));
    fill(scratch, sizeof scratch);
    store_w_add_mul(scratch, i, (int32_t)(i * 99991 + 3));
    assert(rd_w(scratch, off) == (int32_t)(i * 99991 + 3));
    fill(scratch, sizeof scratch);
    store_l_add_mul(scratch, i, (int64_t)(i * 0x100000001LL + 5));
    assert(rd_l(scratch, off) == (int64_t)(i * 0x100000001LL + 5));
  }

  /* add_mul_disp: offset i*4 + 16 */
  for (int64_t i = 0; i < 50; i++) {
    size_t off = (size_t)(i * 4 + 16);
    assert(load_b_add_mul_disp(buf, i) == rd_b(buf, off));
    assert(load_h_add_mul_disp(buf, i) == rd_h(buf, off));
    assert(load_w_add_mul_disp(buf, i) == rd_w(buf, off));
    assert(load_l_add_mul_disp(buf, i) == rd_l(buf, off));

    fill(scratch, sizeof scratch);
    store_b_add_mul_disp(scratch, i, (int8_t)(i + 2));
    assert(rd_b(scratch, off) == (int8_t)(i + 2));
    fill(scratch, sizeof scratch);
    store_h_add_mul_disp(scratch, i, (int16_t)(i * 257 + 9));
    assert(rd_h(scratch, off) == (int16_t)(i * 257 + 9));
    fill(scratch, sizeof scratch);
    store_w_add_mul_disp(scratch, i, (int32_t)(i * 65537 + 11));
    assert(rd_w(scratch, off) == (int32_t)(i * 65537 + 11));
    fill(scratch, sizeof scratch);
    store_l_add_mul_disp(scratch, i, (int64_t)(i * 0x200000003LL + 13));
    assert(rd_l(scratch, off) == (int64_t)(i * 0x200000003LL + 13));
  }

  /* add_mul_disp_neg: offset i*4 - 16 */
  for (int64_t i = 5; i < 60; i++) {
    size_t off = (size_t)(i * 4 - 16);
    assert(load_b_add_mul_disp_neg(buf, i) == rd_b(buf, off));
    assert(load_h_add_mul_disp_neg(buf, i) == rd_h(buf, off));
    assert(load_w_add_mul_disp_neg(buf, i) == rd_w(buf, off));
    assert(load_l_add_mul_disp_neg(buf, i) == rd_l(buf, off));

    fill(scratch, sizeof scratch);
    store_b_add_mul_disp_neg(scratch, i, (int8_t)(i * 3));
    assert(rd_b(scratch, off) == (int8_t)(i * 3));
    fill(scratch, sizeof scratch);
    store_h_add_mul_disp_neg(scratch, i, (int16_t)(i * 521));
    assert(rd_h(scratch, off) == (int16_t)(i * 521));
    fill(scratch, sizeof scratch);
    store_w_add_mul_disp_neg(scratch, i, (int32_t)(i * 0x10001));
    assert(rd_w(scratch, off) == (int32_t)(i * 0x10001));
    fill(scratch, sizeof scratch);
    store_l_add_mul_disp_neg(scratch, i, (int64_t)(i * 0x300000007LL));
    assert(rd_l(scratch, off) == (int64_t)(i * 0x300000007LL));
  }
}
