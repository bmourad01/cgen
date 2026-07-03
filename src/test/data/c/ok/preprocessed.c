#define LIMIT 10
#define SQUARE(x) ((x) * (x))

int
sumsq(int n) {
  int total = 0;
  for (int i = 0; i < LIMIT; i++)
    total += SQUARE(i);
  return total + n;
}
