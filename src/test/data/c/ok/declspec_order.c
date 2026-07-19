/* Type qualifiers may be interleaved with the type-specifier keywords in any
   order (C99 §6.7.2 ¶2): `unsigned const char` means `const unsigned char`. */

unsigned const char a = 1;
const unsigned char b = 2;
unsigned char const c = 3;
long const unsigned int d = 4;
static unsigned const long e = 5;
volatile unsigned f;

int
sum(void) {
  return a + b + c + (int)d + (int)e;
}
