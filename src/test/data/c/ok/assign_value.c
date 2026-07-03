/* The value of an assignment `lhs = rhs` is the right operand converted and
   evaluated *once* (§6.5.16.1), not a re-evaluation of the RHS at the point
   the value is used. The same applies to a compound assignment (§6.5.16.2). */

int g = 9;
int *p = &g;

int
self_ref(void) {
  int r = (*p = 1 < *p);
  if (r)
    *p = 0;
  return *p;
}

int g2 = 5;
int *q = &g2;
int
compound_self(void) {
  return (*q += *q);
}

int
incdec(void) {
  int x = 6;
  int a = x++; /* a = 6, x = 7 */
  int b = ++x; /* b = 8, x = 8 */
  return a * 100 + b * 10 + x;
}

int
chain(void) {
  int a, b, c;
  a = b = c = 7;
  return a + b + c;
}

int
cond_assign(void) {
  int x = 0;
  if ((x = 5))
    return x;
  return -1;
}
