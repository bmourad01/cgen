#include <assert.h>

extern unsigned char popcnt8(unsigned char n);
extern unsigned short popcnt16(unsigned short n);
extern unsigned int popcnt32(unsigned int n);
extern unsigned long popcnt64(unsigned long n);

int main() {
  assert(popcnt8(0xFF) == 8);
  assert(popcnt8(0x0F) == 4);

  assert(popcnt16(0xFFFF) == 16);
  assert(popcnt16(0x00FF) == 8);

  assert(popcnt32(0xFFFFFFFF) == 32);
  assert(popcnt32(0x0000FFFF) == 16);

  assert(popcnt64(0xFFFFFFFFFFFFFFFF) == 64);
  assert(popcnt64(0x00000000FFFFFFFF) == 32);
}
