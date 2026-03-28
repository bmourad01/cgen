#include <assert.h>

extern unsigned fnv1a(const char *data, long len);
extern unsigned popcount32(unsigned x);
extern int dot_product(const int *a, const int *b, int n);
extern int nested_licm(int x, int n, int m);
extern void transform_array(int *dst, const int *src, int n);
extern int div_chain_w(unsigned x);
extern long div_chain_l(long x);
extern void *binary_search(const void *key, const void *base, long nel,
                           long width, int (*cmp)(const void *, const void *));
extern int spill_stress(int n);
extern int cse_diamond(int x, int y, int z);
extern int cse_multi(int a, int b, int c, int d);
extern int identities(int x, int y);
extern long fib(long n);
extern double fsum(const double *arr, int n);
extern int sroa_sum(int a, int b, int c, int d, int e, int f);
extern int bitops(int x, int shift);
extern long cgen_strlen(const char *s);
extern long int_pow(long base, long exp);
extern int ackermann(int m, int n);

static int
intcmp(const void *a, const void *b) {
  int x = *(const int *)a, y = *(const int *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

int
main() {
  assert(popcount32(0) == 0);
  assert(popcount32(1) == 1);
  assert(popcount32(0xffffffff) == 32);
  assert(popcount32(0x55555555) == 16);
  assert(popcount32(0x80000001) == 2);

  assert(fib(0) == 0);
  assert(fib(1) == 1);
  assert(fib(10) == 55);
  assert(fib(20) == 6765);

  assert(ackermann(0, 0) == 1);
  assert(ackermann(1, 3) == 5);
  assert(ackermann(2, 2) == 7);
  assert(ackermann(3, 2) == 29);

  assert(identities(0, 42) == 0);
  assert(identities(7, 0) == 7);
  assert(identities(-1, 100) == -1);

  assert(sroa_sum(1, 2, 3, 4, 5, 6) == 21);
  assert(sroa_sum(0, 0, 0, 0, 0, 0) == 0);
  assert(sroa_sum(-1, 1, -1, 1, -1, 1) == 0);

  assert(int_pow(2, 10) == 1024);
  assert(int_pow(3, 5) == 243);
  assert(int_pow(7, 0) == 1);
  assert(int_pow(1, 100) == 1);

  assert(nested_licm(1, 3, 2) == 192);
  assert(nested_licm(0, 5, 5) == 350);
  assert(nested_licm(0, 0, 5) == 0);

  {
    int a[] = {1, 2, 3, 4, 5};
    int b[] = {5, 4, 3, 2, 1};
    assert(dot_product(a, b, 5) == 35);
    assert(dot_product(a, b, 0) == 0);
  }

  assert(div_chain_w(0) == 0);
  assert(div_chain_w(100) == 82);

  assert(div_chain_l(0) == 0);
  assert(div_chain_l(100) == 66);

  assert(fnv1a("", 0) == 2166136261u);

  assert(cgen_strlen("") == 0);
  assert(cgen_strlen("hello") == 5);
  assert(cgen_strlen("hello, world") == 12);

  {
    double arr[] = {1.0, 2.0, 3.0, 4.0, 5.0};
    assert(fsum(arr, 0) == 0.0);
    assert(fsum(arr, 5) == 15.0);
  }

  assert(spill_stress(1) == 60);

  assert(cse_diamond(2, 3, 4) == 14);
  assert(cse_diamond(0, 0, 0) == 0);

  assert(cse_multi(2, 3, 4, 5) == 17);
  assert(cse_multi(0, 0, 0, 0) == 0);

  {
    int src[] = {0, 1, 2, 3};
    int dst[4];
    int expected[] = {7, 10, 12, 17};
    transform_array(dst, src, 4);
    for (int i = 0; i < 4; i++)
      assert(dst[i] == expected[i]);
  }

  {
    int arr[] = {1, 3, 5, 7, 9, 11, 13};
    int n = 7;
    int key;
    key = 7;
    assert(binary_search(&key, arr, n, sizeof(int), intcmp) == &arr[3]);
    key = 1;
    assert(binary_search(&key, arr, n, sizeof(int), intcmp) == &arr[0]);
    key = 13;
    assert(binary_search(&key, arr, n, sizeof(int), intcmp) == &arr[6]);
    key = 6;
    assert(binary_search(&key, arr, n, sizeof(int), intcmp) == 0);
  }
}
