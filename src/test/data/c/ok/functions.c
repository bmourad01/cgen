int
add(int a, int b) {
  return a + b;
}

int
twice(int x) {
  return add(x, x);
}

int
apply(int (*f)(int), int v) {
  return f(v);
}
