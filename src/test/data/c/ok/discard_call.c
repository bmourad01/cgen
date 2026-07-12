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

void
bump(void) {
  counter += 3;
}

/* A void-returning call in the discarded left operand of a comma (§6.5.17) */
int
comma_void(void) {
  counter = 0;
  int v = (bump(), 42);
  return v + counter;
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
