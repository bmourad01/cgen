#include <stdio.h>

extern int foo(unsigned int x);

unsigned int nth(int n) {
  unsigned int x = 1;
  unsigned int i = 0;
  while (1) {
    if (foo(x)) {
      if (++i == n) {
        return x;
      }
    }
    ++x;
  }
}

int main() {
  for (unsigned int i = 1; i <= 20; ++i) {
    printf("%d\n", nth(i));
  }
}
