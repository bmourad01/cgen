/* A function designator is not a modifiable lvalue (C99 §6.3.2.1). */

void g(void);

void
f(void) {
  g = 0;
}
