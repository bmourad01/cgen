#include <assert.h>
#include <stdint.h>

/* narrow loads */
extern uint8_t ld_b(const void *p);
extern uint16_t ld_h(const void *p);

/* narrow immediate moves */
extern uint8_t zero_b(void);
extern uint16_t zero_h(void);
extern uint8_t const_b(void);
extern uint16_t const_h(void);

/* narrow arith */
extern uint8_t add_b(uint8_t x, uint8_t y);
extern uint16_t add_h(uint16_t x, uint16_t y);
extern uint8_t add_bi(uint8_t x);
extern uint16_t add_hi(uint16_t x);
extern uint8_t sub_b(uint8_t x, uint8_t y);
extern uint16_t sub_h(uint16_t x, uint16_t y);
extern uint8_t sub_bi(uint8_t x);
extern uint16_t sub_hi(uint16_t x);
extern uint8_t sub_ib(uint8_t x);
extern uint16_t sub_ih(uint16_t x);

/* narrow bitwise */
extern uint8_t and_b(uint8_t x, uint8_t y);
extern uint16_t and_h(uint16_t x, uint16_t y);
extern uint8_t or_b(uint8_t x, uint8_t y);
extern uint16_t or_h(uint16_t x, uint16_t y);
extern uint8_t xor_b(uint8_t x, uint8_t y);
extern uint16_t xor_h(uint16_t x, uint16_t y);
extern uint8_t and_bi(uint8_t x);
extern uint16_t or_hi(uint16_t x);
extern uint8_t xor_bi(uint8_t x);
extern uint8_t xor_b_self(uint8_t x);
extern uint16_t xor_h_self(uint16_t x);

/* narrow unary */
extern uint8_t neg_b(uint8_t x);
extern uint16_t neg_h(uint16_t x);
extern uint8_t not_b(uint8_t x);
extern uint16_t not_h(uint16_t x);

/* narrow shifts */
extern uint8_t lsl_b(uint8_t x, uint8_t y);
extern uint16_t lsl_h(uint16_t x, uint16_t y);
extern uint8_t lsr_b(uint8_t x, uint8_t y);
extern uint16_t lsr_h(uint16_t x, uint16_t y);
extern uint8_t asr_b(uint8_t x, uint8_t y);
extern uint16_t asr_h(uint16_t x, uint16_t y);
extern uint8_t lsl_bi(uint8_t x);
extern uint16_t lsr_hi(uint16_t x);

int
main(void) {
  {
    uint8_t buf[2] = {0x9C, 0xA5};
    assert(ld_b(buf) == 0x9C);
    /* ld.h reads 2 bytes little-endian: buf[0] | buf[1]<<8 */
    assert(ld_h(buf) == (uint16_t)0xA59C);
  }

  assert(zero_b() == 0);
  assert(zero_h() == 0);
  assert(const_b() == 7);
  assert(const_h() == 256);

  /* in-range: 3 + 4 = 7 */
  assert(add_b(3, 4) == 7);
  assert(add_h(3, 4) == 7);
  /* wrap at 8 bits: 0xFF + 1 = 0x00 */
  assert(add_b(0xFF, 1) == 0x00);
  /* wrap at 16 bits: 0xFFFF + 1 = 0x0000 */
  assert(add_h(0xFFFF, 1) == 0x0000);
  /* no wrap into the high half: high-bit-set operands shouldn't leak
     upper garbage into low 8/16 bits */
  assert(add_b(0x80, 0x80) == 0x00);
  assert(add_h(0x8000, 0x8000) == 0x0000);
  /* immediate variants: +3 */
  assert(add_bi(5) == 8);
  assert(add_hi(5) == 8);
  assert(add_bi(0xFD) == 0x00);
  assert(add_hi(0xFFFD) == 0x0000);

  assert(sub_b(10, 3) == 7);
  assert(sub_h(10, 3) == 7);
  /* underflow wrap */
  assert(sub_b(0, 1) == 0xFF);
  assert(sub_h(0, 1) == 0xFFFF);
  /* immediate variants (x - 3) */
  assert(sub_bi(10) == 7);
  assert(sub_hi(10) == 7);
  assert(sub_bi(0) == 0xFD);
  assert(sub_hi(0) == 0xFFFD);
  /* reverse variants (100 - x) */
  assert(sub_ib(30) == 70);
  assert(sub_ih(30) == 70);
  assert(sub_ib(200) == (uint8_t)(100 - 200));      /* 0x9C */
  assert(sub_ih(65000) == (uint16_t)(100 - 65000)); /* 0x026C */

  assert(and_b(0xF0, 0x0F) == 0x00);
  assert(and_b(0xFF, 0x12) == 0x12);
  assert(and_h(0xF0F0, 0x0F0F) == 0x0000);
  assert(and_h(0xFFFF, 0x1234) == 0x1234);

  assert(or_b(0xF0, 0x0F) == 0xFF);
  assert(or_b(0x01, 0x80) == 0x81);
  assert(or_h(0xF000, 0x000F) == 0xF00F);
  assert(or_h(0x0001, 0x8000) == 0x8001);

  assert(xor_b(0xF0, 0x0F) == 0xFF);
  assert(xor_b(0xFF, 0xFF) == 0x00);
  assert(xor_h(0xF000, 0x0F0F) == 0xFF0F);
  assert(xor_h(0x1234, 0x4321) == 0x5115);

  /* bitwise with immediates */
  assert(and_bi(0xFF) == 0x0F); /* x & 15 */
  assert(and_bi(0xF0) == 0x00);
  assert(or_hi(0x1200) == 0x12FF); /* x | 255 */
  assert(or_hi(0x0000) == 0x00FF);
  assert(xor_bi(0x00) == 0x2A); /* x ^ 42 */
  assert(xor_bi(0x2A) == 0x00);

  /* xor with self: always 0 */
  for (uint32_t v = 0; v < 256; v += 37) {
    assert(xor_b_self((uint8_t)v) == 0);
  }
  for (uint32_t v = 0; v < 65536; v += 1237) {
    assert(xor_h_self((uint16_t)v) == 0);
  }

  assert(neg_b(0) == 0);
  assert(neg_b(1) == 0xFF);
  assert(neg_b(0x80) == 0x80);
  assert(neg_b(0x7F) == 0x81);
  assert(neg_h(0) == 0);
  assert(neg_h(1) == 0xFFFF);
  assert(neg_h(0x8000) == 0x8000);
  assert(neg_h(0x7FFF) == 0x8001);

  assert(not_b(0x00) == 0xFF);
  assert(not_b(0xAA) == 0x55);
  assert(not_h(0x0000) == 0xFFFF);
  assert(not_h(0x1234) == 0xEDCB);

  /* lsl: logical shift left */
  assert(lsl_b(0x01, 0) == 0x01);
  assert(lsl_b(0x01, 3) == 0x08);
  assert(lsl_b(0xFF, 1) == 0xFE);
  assert(lsl_h(0x0001, 15) == 0x8000);
  assert(lsl_h(0x00FF, 4) == 0x0FF0);

  /* lsr: logical shift right (zero fill) */
  assert(lsr_b(0xFF, 0) == 0xFF);
  assert(lsr_b(0xFF, 1) == 0x7F);
  assert(lsr_b(0x80, 7) == 0x01);
  assert(lsr_h(0xFFFF, 1) == 0x7FFF);
  assert(lsr_h(0x8000, 15) == 0x0001);

  /* asr: arithmetic shift right (sign fill) */
  assert(asr_b(0x7F, 1) == 0x3F);
  assert(asr_b(0x80, 1) == 0xC0); /* sign-extends the high bit of the byte */
  assert(asr_b(0xFF, 7) == 0xFF);
  assert(asr_h(0x7FFF, 1) == 0x3FFF);
  assert(asr_h(0x8000, 1) == 0xC000);
  assert(asr_h(0xFFFF, 15) == 0xFFFF);

  /* shift by constant amount */
  assert(lsl_bi(0x01) == 0x08); /* x << 3 */
  assert(lsl_bi(0xFF) == 0xF8);
  assert(lsr_hi(0xFFFF) == 0x0FFF); /* x >> 4 */
  assert(lsr_hi(0x1000) == 0x0100);
}
