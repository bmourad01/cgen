typedef int binop_t(int a, int b);
typedef int (*binop_ptr)(int, int);

struct calculator {
  binop_t *op;
  binop_ptr fallback;
};

static int
add(int a, int b) {
  return a + b;
}
static int
mul(int a, int b) {
  return a * b;
}

int
run(struct calculator *c, int x, int y) {
  return c->op(x, y) + c->fallback(x, y);
}

int
compute(int x, int y) {
  struct calculator c;
  c.op = add;
  c.fallback = mul;
  return run(&c, x, y);
}
