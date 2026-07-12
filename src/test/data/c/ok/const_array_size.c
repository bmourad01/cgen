/* Block-scope array bounds are integer constant expressions (§6.7.6.2),
   folded during elaboration; they need not be literals. */

enum { N = 7 };

unsigned long
size_sizeof(void) {
  void *a[sizeof(void *) * 8 * 3 / 2]; /* 96 elements */
  return sizeof a;                     /* 96 * 8 = 768 */
}

unsigned long
size_arith(void) {
  int b[2 + 3 * 4]; /* 14 */
  return sizeof b;  /* 14 * 4 = 56 */
}

unsigned long
size_enum(void) {
  char c[N * 2]; /* 14 */
  return sizeof c;
}

int
roundtrip(void) {
  int a[sizeof(void *) * 8 * 3 / 2]; /* 96 */
  a[95] = 42;
  return a[95];
}
