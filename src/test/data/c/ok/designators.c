/* Nested designators in initializers (C99 §6.7.8). Each function packs
   the initialized fields into a single int so the driver can check the
   exact placement. */

struct Inner {
  int a;
  int b;
};
struct Outer {
  struct Inner s;
  int x;
};

int
single_chain(void) {
  struct Outer o = {.s.b = 5};
  return o.s.a * 100 + o.s.b * 10 + o.x; /* 050 */
}

int
merge(void) {
  struct Outer o = {.s.a = 1, .s.b = 2, .x = 9};
  return o.s.a * 100 + o.s.b * 10 + o.x; /* 129 */
}

int
continuation(void) {
  struct Outer o = {.s.a = 1, 2, 3};
  return o.s.a * 100 + o.s.b * 10 + o.x; /* 123 */
}

int
brace_then_reset(void) {
  struct Outer o = {.x = 9, .s = {1, 2}};
  return o.s.a * 100 + o.s.b * 10 + o.x; /* 129 */
}

int
array_desig(void) {
  int a[6] = {[4] = 29, [2] = 15};
  return a[0] + a[2] + a[4]; /* 44 */
}

int
elem_field(void) {
  struct Inner ps[3] = {[1].b = 7, [1].a = 4, [0].a = 1};
  return ps[0].a * 1000 + ps[1].a * 100 + ps[1].b * 10 + ps[2].a; /* 1470 */
}

int
multidim(void) {
  int m[2][2] = {[0][1] = 3, [1][0] = 5};
  return m[0][0] + m[0][1] * 10 + m[1][0] * 100 + m[1][1] * 1000; /* 530 */
}

int
override(void) {
  int a[3] = {[1] = 1, [1] = 7};
  return a[0] * 100 + a[1] * 10 + a[2]; /* 070 */
}

struct Inner
make_inner(void) {
  struct Inner i = {7, 8};
  return i;
}

int
overlay_call(void) {
  struct Outer o = {.s = make_inner(), .s.b = 3}; /* s = {7, 3}, x = 0 */
  return o.s.a * 100 + o.s.b * 10 + o.x;          /* 730 */
}

int
overlay_literal(void) {
  struct Outer o = {.s = (struct Inner){1, 2}, .s.b = 3};
  return o.s.a * 100 + o.s.b * 10 + o.x; /* 130 */
}

static const struct Outer go = {.s = (struct Inner){4, 5}, .s.b = 6, .x = 7};

int
overlay_global(void) {
  return go.s.a * 1000 + go.s.b * 100 + go.x * 10; /* 4670 */
}
