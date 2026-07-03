int
gcd(int a, int b) {
  while (b != 0) {
    int t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int
sumto(int n) {
  int s = 0;
  for (int i = 1; i <= n; i++)
    s += i;
  return s;
}

long
fib(int n) {
  if (n < 2)
    return n;
  return fib(n - 1) + fib(n - 2);
}
