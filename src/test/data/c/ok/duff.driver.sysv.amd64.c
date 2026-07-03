#include <assert.h>

extern void copy(int *dst, const int *src, int count);
extern int scoped(int sel, int limit);

int
main(void) {
  int src[300], dst[300];
  int i, count;

  for (count = 1; count <= 260; count++) {
    for (i = 0; i < 300; i++) {
      src[i] = i * 7 + 3;
      dst[i] = -1;
    }
    copy(dst, src, count);
    for (i = 0; i < count; i++)
      assert(dst[i] == i * 7 + 3);
    assert(dst[count] == -1);
  }

  assert(scoped(0, 0) == 1);
  assert(scoped(0, 1) == 2);
  assert(scoped(0, 5) == 7);
  assert(scoped(1, 0) == 1);
  assert(scoped(1, 1) == 2);
  assert(scoped(1, 5) == 7);
  assert(scoped(9, 0) == -1);

  return 0;
}
