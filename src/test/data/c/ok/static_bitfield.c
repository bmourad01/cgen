struct flags {
  unsigned a : 3;
  unsigned b : 5;
  signed c : 4;
  int x;
};

struct mixed {
  int p : 10;
  int : 0;
  int q : 10;
  unsigned r : 1;
};

static struct flags gf = {5, 20, -2, 0x1234};
static struct mixed gm = {-100, 300, 1};

unsigned
f_a(void) {
  return gf.a;
}

unsigned
f_b(void) {
  return gf.b;
}

int
f_c(void) {
  return gf.c;
}

int
f_x(void) {
  return gf.x;
}

int
m_p(void) {
  return gm.p;
}

int
m_q(void) {
  return gm.q;
}

unsigned
m_r(void) {
  return gm.r;
}
