#include <assert.h>

unsigned char even(int n);
unsigned char odd(int n);

int
main() {
  for (int i = 0; i < 100; i++) {
    if (i & 1) {
      assert(!even(i));
      assert(odd(i));
    } else {
      assert(even(i));
      assert(!odd(i));
    }
  }
}
