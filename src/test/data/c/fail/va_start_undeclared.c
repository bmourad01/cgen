typedef __builtin_va_list va_list;

int
f(int n, ...) {
  va_list ap;
  __builtin_va_start(ap, undeclared);
  return 0;
}
