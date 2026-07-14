struct S {
  int x;
} s;

int
f(void) {
  int acc = s;
  return acc;
}
