/* C99 6.7.8p5: a block-scope identifier with external linkage shall
   have no initializer. */
int
f(void) {
  extern int x = 5;
  return x;
}
