/* Examples taken from:
 * https://people.eecs.berkeley.edu/~necula/cil/cil016.html
 */

int
f1(void) {
  int x;
  return x == (1 && x);
}

int
f2(void) {
  return ((1 - sizeof(int)) >> 32);
}

int x3 = 5;
int
f3() {
  int x3 = 3;
  {
    extern int x3;
    return x3;
  }
}

int (*pf)(void);
int
f4(void) {
  pf = &f4;
  pf = ***f4;
  pf();
  (****pf)();
  (***************f4)();
}

struct {
  int x;
  struct {
    int y, z;
  } nested;
} i = {.nested.y = 5, 6, .x = 1, 2};

typedef struct {
  char *key;
  char *value;
} T1;

typedef struct {
  long type;
  char *value;
} T3;

T1 a[] = {{"", ((char *)&((T3){1, (char *)1}))}};

int
f6() {
  T3 *pt3 = (T3 *)a[0].value;
  return pt3->value;
}

int
f7(void) {
  return ((int[]){1, 2, 3, 4})[1];
}

int
foo8() {
  static bar();
  static (*pbar)() = bar;
}

static bar() {
  return 1;
}

static (*pbar)() = 0;

unsigned long
foo9() {
  return (unsigned long)-1 / 8;
}
