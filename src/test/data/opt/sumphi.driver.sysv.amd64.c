#include <assert.h>

struct t {
  int a;
  int b;
};

int sumphi(struct t a, struct t b, int x);

int
main() {
  struct t s1 = {3, 4};
  struct t s2 = {10, -2};
  int res1 = sumphi(s1, s2, -1);
  assert(res1 == 7);
  int res2 = sumphi(s1, s2, 0);
  assert(res2 == 8);

  struct t s3 = {5, 6};
  struct t s4 = {100, 200};
  int res3 = sumphi(s3, s4, -5);
  int res4 = sumphi(s3, s4, 42);
  assert(res3 == 11);
  assert(res4 == 300);
  return 0;
}
