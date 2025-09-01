#include <assert.h>

extern void foo(int *dst, int *src, unsigned int n);

int main() {
  int dst[3];
  int src[3] = {1, 2, 3};
  foo(dst, src, 3);
  assert(dst[0] + dst[1] + dst[2] == 6);
}
