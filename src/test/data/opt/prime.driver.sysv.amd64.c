#define N 20

extern int foo(unsigned int n);

int main() {
  int n = 1;
  int i = 0;
  while (1) {
    if (foo(n)) {
      if (++i == N) {
        return n;
      }
    }
    ++n;
  }
  return 0;
}
