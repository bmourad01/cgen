/* A typedef may be redefined to denote the same type (C11 §6.7 ¶3; a
   GCC/Clang extension in C99). */
typedef unsigned int uint;
typedef unsigned int uint;

typedef struct Ins Ins;
struct Ins {
  int op;
  int arg;
};

int
ins_size(void) {
  return (int)sizeof(Ins);
}

int
ins_field(void) {
  Ins i;
  i.op = 7;
  i.arg = 35;
  return i.op + i.arg;
}

/* Enum constants have type `int` and convert freely to and from enum-typed
   objects (§6.7.2.2: an enum is an integer type). */
enum pool { PHeap, PBody, PFn };

int
pool_of(int n) {
  enum pool p;
  p = n;    /* int -> enum */
  return p; /* enum -> int */
}

/* The predefined identifier `__func__` (C99 §6.4.2.2). */
const char *
whoami(void) {
  return __func__;
}
