#include <assert.h>

extern int leading_zeros(unsigned int);
extern int trailing_zeros(unsigned int);
extern int set_bits(unsigned int);
extern int leading_zeros_l(unsigned long);
extern int trailing_zeros_l(unsigned long);
extern int set_bits_l(unsigned long);
extern int set_bits_ll(unsigned long long);
extern unsigned short swap16(unsigned short);
extern unsigned int swap32(unsigned int);
extern unsigned long swap64(unsigned long);
extern int first_set(int);
extern int first_set_l(long);
extern int parity(unsigned int);
extern int parity_ll(unsigned long long);

int
main(void) {
  assert(leading_zeros(1u) == 31);
  assert(leading_zeros(0x80000000u) == 0);
  assert(trailing_zeros(1u) == 0);
  assert(trailing_zeros(0x80000000u) == 31);
  assert(set_bits(0u) == 0);
  assert(set_bits(0xFFFFFFFFu) == 32);
  assert(set_bits(0xAAAAAAAAu) == 16);

  assert(leading_zeros_l(1ul) == 63);
  assert(trailing_zeros_l(0x100ul) == 8);
  assert(set_bits_l(0xFFul) == 8);
  assert(set_bits_ll(0xFFFFFFFFFFFFFFFFull) == 64);
  assert(set_bits_ll(0ull) == 0);

  assert(swap16(0x1234) == 0x3412);
  assert(swap32(0x11223344u) == 0x44332211u);
  assert(swap64(0x0102030405060708ul) == 0x0807060504030201ul);

  assert(first_set(0) == 0);
  assert(first_set(1) == 1);
  assert(first_set(0x10) == 5);
  assert(first_set_l(0x100L) == 9);
  assert(parity(0u) == 0);
  assert(parity(7u) == 1);
  assert(parity(0xFFu) == 0);
  assert(parity_ll(0xFFFFFFFFFFFFFFFFull) == 0);
  return 0;
}
