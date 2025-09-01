#include <stdio.h>
#include <assert.h>

extern unsigned char clz8(unsigned char n);
extern unsigned char ctz8(unsigned char n);

int main() {
  assert(clz8(0b00001111) == 4);
  assert(ctz8(0b00001111) == 0);

  assert(clz8(0b11110000) == 0);
  assert(ctz8(0b11110000) == 4);
}
