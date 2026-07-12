int
plain(int x) {
  return __builtin_expect(x, 0);
}

int
in_branch(int x) {
  if (__builtin_expect(x > 0, 1))
    return 1;
  return 0;
}

long
keeps_type(long x) {
  return __builtin_expect(x + 1, 42);
}

int
nested(int a, int b) {
  return __builtin_expect(a, 0) + __builtin_expect(b, 1);
}

int
const_hint(int x) {
  return __builtin_expect(x, 1 + 2 * 3);
}
