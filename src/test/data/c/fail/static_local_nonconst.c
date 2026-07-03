/* A block-scope static has static storage duration, so its initializer
   must be a constant expression (C99 6.7.8p4); a parameter is not. */
int
f(int n) {
  static int x = n;
  return x;
}
