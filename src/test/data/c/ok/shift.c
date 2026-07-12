long
shl(long a, int b) {
  return a << b;
}

long
sar(long a, int b) {
  return a >> b;
}

unsigned long
shr(unsigned long a, int b) {
  return a >> b;
}

/* A count wider than the value: the count is truncated to the value's
   width for the shift (§6.5.7 promotes the operands independently). */
int
shl_wide(int a, long b) {
  return a << b;
}

int
sar_wide(int a, long b) {
  return a >> b;
}

unsigned
shr_wide(unsigned a, long b) {
  return a >> b;
}
