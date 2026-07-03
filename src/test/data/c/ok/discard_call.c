struct S {
  int a, b;
};

static int counter;

int
add7(void) {
  counter += 7;
  return counter;
}

unsigned
mul(unsigned a, unsigned b) {
  counter += (int)(a * b);
  return a * b;
}

int *
setp(int *p, int v) {
  *p = v;
  return p;
}

struct S
mk(int v) {
  counter += v;
  struct S s = {v, v + 1};
  return s;
}

int
run(void) {
  counter = 0;
  add7();
  add7();
  mul(3, 4);
  int x = 0;
  setp(&x, 99);
  mk(5);
  return counter + x;
}
