#include <assert.h>

extern int analyze_array(int *arr, int n);
extern int analyze_array_inl(int *arr, int n);

int
main() {
  int arr1[] = {3, 1, 4, 1, 5, 9, 2};
  assert(analyze_array(arr1, 7) == 229);
  assert(analyze_array_inl(arr1, 7) == 229);

  int arr2[] = {1, 2, 3};
  assert(analyze_array(arr2, 3) == 21);
  assert(analyze_array_inl(arr2, 3) == 21);

  int arr3[] = {5, 5, 5};
  assert(analyze_array(arr3, 3) == 75);
  assert(analyze_array_inl(arr3, 3) == 75);

  int arr4[] = {1};
  assert(analyze_array(arr4, 1) == 1);
  assert(analyze_array_inl(arr4, 1) == 1);

  int arr5[] = {1, 2, 3, 4, 5};
  assert(analyze_array(arr5, 5) == 81);
  assert(analyze_array_inl(arr5, 5) == 81);

  int arr6[] = {6, 5, 4, 3, 2, 1};
  assert(analyze_array(arr6, 6) == 131);
  assert(analyze_array_inl(arr6, 6) == 131);

  int arr7[] = {1, 2, 1, 2, 1, 2, 1, 2};
  assert(analyze_array(arr7, 8) == 28);
  assert(analyze_array_inl(arr7, 8) == 28);
}
