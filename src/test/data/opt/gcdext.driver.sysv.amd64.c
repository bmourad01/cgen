struct S {
  int gcd;
  int x;
  int y;
};

extern struct S gcd(int a, int b);

int main() {
  struct S s = gcd(12, 18);
  return s.gcd;
}
