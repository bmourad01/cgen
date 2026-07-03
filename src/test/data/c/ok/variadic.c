typedef __builtin_va_list va_list;

int
sum(int n, ...) {
  va_list ap;
  __builtin_va_start(ap, n);
  int total = 0;
  for (int i = 0; i < n; i = i + 1)
    total = total + __builtin_va_arg(ap, int);
  __builtin_va_end(ap);
  return total;
}

double
dsum(int n, ...) {
  __builtin_va_list ap;
  __builtin_va_start(ap, n);
  double total = 0;
  for (int i = 0; i < n; i = i + 1)
    total = total + __builtin_va_arg(ap, double);
  __builtin_va_end(ap);
  return total;
}

struct P {
  int a;
  int b;
};

int
psum(int n, ...) {
  va_list ap;
  __builtin_va_start(ap, n);
  int total = 0;
  for (int i = 0; i < n; i = i + 1) {
    struct P p = __builtin_va_arg(ap, struct P);
    total = total + p.a + p.b;
  }
  __builtin_va_end(ap);
  return total;
}

int
sum3(int a, int b, int c) {
  return sum(3, a, b, c);
}
