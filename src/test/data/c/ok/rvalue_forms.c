/* Lvalue forms applied to an rvalue operand, and aggregate conditionals.
   These are legal C (§6.5.2.3, §6.5.2.1, §6.5.15) that require materializing
   or selecting a value that has no named storage. */

struct S {
  int base;
  int x;
};

struct S
make(int v) {
  struct S s;
  s.base = v + 1;
  s.x = v + 2;
  return s;
}

/* Member access on an rvalue structure (a call result): §6.5.2.3 ¶3 makes
   `make(v).base` an rvalue. */
int
m_base(int v) {
  return make(v).base;
}
int
m_x(int v) {
  return make(v).x;
}

int
idx_cast(unsigned char *p, int i) {
  return ((unsigned char *)p)[i];
}
int
idx_arith(int *p, int i) {
  return (p + 1)[i];
}

/* A struct-typed conditional (§6.5.15): both arms have structure type, so
   the result is an rvalue structure. */
struct S s_a = {10, 20};
struct S s_b = {30, 40};

int
cond_base(int c) {
  return (c ? s_a : s_b).base;
}
int
cond_x(int c) {
  return (c ? s_a : s_b).x;
}

struct S
cond_ptr(int c, struct S *a, struct S *b) {
  return c ? *a : *b;
}
