struct point {
  int x;
  int y;
};

struct padded {
  char c;
  int n;
};

int g_int = 42;
long g_long = 1234567;
char *g_msg = "hello";
int g_arr[4] = {10, 20, 30, 40};
int g_sparse[5] = {1, 2};
char g_name[8] = "abc";

/* Exactly sized: no room for the terminator, which C99 6.7.8p14 drops. */
char g_exact[3] = "abc";

char g_flex[] = "abc";
char g_empty[4] = "";
struct point g_pt = {3, 4};
struct padded g_pad = {7, 100};
struct point g_pts[2] = {{1, 2}, {3, 4}};

/* Address constants (C99 6.6p7): the address of an array element or struct
   member of a static object, and a null pointer. */
int *g_pelem = &g_arr[2];

int *g_pmemb = &g_pt.y;
int *g_pnull = (void *)0;
const int *g_pconst = &g_int;
const int *g_pcelem = &g_arr[1];
const int *g_pcarr[3] = {&g_int, (void *)0, &g_arr[3]};

int
get_int(void) {
  return g_int;
}
long
get_long(void) {
  return g_long;
}
char
get_msg(int i) {
  return g_msg[i];
}
int
get_arr(int i) {
  return g_arr[i];
}
int
get_sparse(int i) {
  return g_sparse[i];
}
char
get_name(int i) {
  return g_name[i];
}
char
get_exact(int i) {
  return g_exact[i];
}
char
get_flex(int i) {
  return g_flex[i];
}
char
get_empty(int i) {
  return g_empty[i];
}
int
pt_x(void) {
  return g_pt.x;
}
int
pt_y(void) {
  return g_pt.y;
}
int
pad_c(void) {
  return g_pad.c;
}
int
pad_n(void) {
  return g_pad.n;
}

int
pts_sum(void) {
  return g_pts[0].x + g_pts[0].y + g_pts[1].x + g_pts[1].y;
}

int
deref_pelem(void) {
  return *g_pelem;
}
int
deref_pmemb(void) {
  return *g_pmemb;
}
int
pnull_null(void) {
  return g_pnull == (void *)0;
}
int
deref_pconst(void) {
  return *g_pconst;
}
int
deref_pcelem(void) {
  return *g_pcelem;
}
int
pcarr_get(int i) {
  const int *p = g_pcarr[i];
  return p ? *p : -1;
}
