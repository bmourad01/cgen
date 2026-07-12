/* VLAs are not yet supported, but we want the right error location in the
 * meantime */
short
g(void) {
  return 1;
}
long
f(void) {
  double a[10 + g()];
  return sizeof(a);
}
