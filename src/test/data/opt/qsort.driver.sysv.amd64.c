#include <assert.h>
#include <stdio.h>

extern void qsort(int *arr, long low, long high);

int
main() {
  int arr[] = {10, 7, 8, 9, 1, 5, 22, 59, 6, 17, 54};
  int n = sizeof(arr) / sizeof(arr[0]);
  qsort(arr, 0, n - 1);
  for (int i = 0; i < n; i++) {
    printf("%d\n", arr[i]);
  }
}
