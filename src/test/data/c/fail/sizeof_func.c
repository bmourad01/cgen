/* sizeof shall not be applied to a function type (C99 §6.5.3.4). */

void g(void);

unsigned long
f(void) {
  return sizeof g;
}
