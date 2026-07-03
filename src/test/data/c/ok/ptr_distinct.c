int
cross_assign(int x) {
  int *q = &x;
  unsigned *p = q;
  return (p == q) && (*p == (unsigned)x);
}

int
deep_ne(signed char ***a, signed char ***b) {
  const signed char ***ca = a;
  return ca != b;
}
