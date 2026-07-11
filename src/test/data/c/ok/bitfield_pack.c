struct A {
  char a;
  int b : 4;
  unsigned c : 20;
  short d;
};
struct B {
  int x : 4;
  short y;
  int z : 4;
  char w;
};
struct C {
  char a;
  int : 0;
  char b;
};

unsigned long
size_a(void) {
  return sizeof(struct A);
}
unsigned long
size_b(void) {
  return sizeof(struct B);
}
unsigned long
size_c(void) {
  return sizeof(struct C);
}

int
a_a(struct A *p) {
  return p->a;
}
int
a_b(struct A *p) {
  return p->b;
}
unsigned
a_c(struct A *p) {
  return p->c;
}
int
a_d(struct A *p) {
  return p->d;
}
void
set_b(struct A *p, int v) {
  p->b = v;
}
void
set_c(struct A *p, unsigned v) {
  p->c = v;
}

int
b_x(struct B *p) {
  return p->x;
}
int
b_y(struct B *p) {
  return p->y;
}
int
b_z(struct B *p) {
  return p->z;
}
int
b_w(struct B *p) {
  return p->w;
}

int
c_a(struct C *p) {
  return p->a;
}
int
c_b(struct C *p) {
  return p->b;
}

struct E {
  long long x : 4;
  char arr[4];
  int y : 8;
};

unsigned long
size_e(void) {
  return sizeof(struct E);
}

struct P {
  unsigned lo : 3;
  int mid : 30;
  unsigned hi : 13;
  char tail;
} __attribute__((packed));

unsigned long
size_p(void) {
  return sizeof(struct P);
}
unsigned
p_lo(struct P *p) {
  return p->lo;
}
int
p_mid(struct P *p) {
  return p->mid;
}
unsigned
p_hi(struct P *p) {
  return p->hi;
}
int
p_tail(struct P *p) {
  return p->tail;
}
void
set_mid(struct P *p, int v) {
  p->mid = v;
}
void
set_hi(struct P *p, unsigned v) {
  p->hi = v;
}

struct A init_a = {0x7f, -3, 100000, 12345};
struct E init_e = {6, {10, 20, 30, 40}, 100};
struct P init_p = {5, -1000000, 5000, 0x33};

int
ip_mid(void) {
  return init_p.mid;
}
unsigned
ip_hi(void) {
  return init_p.hi;
}

int
ia_a(void) {
  return init_a.a;
}
int
ia_b(void) {
  return init_a.b;
}
unsigned
ia_c(void) {
  return init_a.c;
}
int
ia_d(void) {
  return init_a.d;
}
long long
ie_x(void) {
  return init_e.x;
}
int
ie_arr(int i) {
  return init_e.arr[i];
}
int
ie_y(void) {
  return init_e.y;
}
