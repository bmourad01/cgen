int
compute(int a, int b) {
  int c = a * b + (a - b) / 2;
  int d = (a > b) ? a : b;
  int e = (a & b) | (a ^ b);
  int f = (a && b) || !c;
  c += d;
  c <<= 1;
  return c + e + f;
}
