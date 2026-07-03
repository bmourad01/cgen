struct point {
  int x;
  int y;
};

struct point
mkpoint(int x, int y) {
  struct point p;
  p.x = x;
  p.y = y;
  return p;
}

int
dot(struct point a, struct point b) {
  return a.x * b.x + a.y * b.y;
}

int
sum_array(int *a, int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    s += a[i];
  return s;
}
