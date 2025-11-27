#include <stdio.h>

extern void *bsearch(const void *key, const void *base, size_t nel,
                     size_t width, int (*cmp)(const void *, const void *));

extern int intcmp(const void *a, const void *b);

static void test_bsearch(const int *arr, size_t n, int key) {
  const int *res = bsearch(&key, arr, n, sizeof(int), intcmp);
  if (res) {
    printf("found %d at index %ld, value %d\n", key, (long)(res - arr), *res);
  } else {
    printf("%d not found\n", key);
  }
}

int main() {
  int arr[] = {-10, -3, -1, 0, 1, 2, 4, 7, 10, 25, 100};

  size_t n = sizeof(arr) / sizeof(arr[0]);

  /* found */
  test_bsearch(arr, n, -10);
  test_bsearch(arr, n, -1);
  test_bsearch(arr, n, 0);
  test_bsearch(arr, n, 4);
  test_bsearch(arr, n, 25);
  test_bsearch(arr, n, 100);

  /* not found */
  test_bsearch(arr, n, -11);
  test_bsearch(arr, n, -2);
  test_bsearch(arr, n, 3);
  test_bsearch(arr, n, 5);
  test_bsearch(arr, n, 8);
  test_bsearch(arr, n, 99);
  test_bsearch(arr, n, 101);
}
