struct flags {
  unsigned ready : 1;
  unsigned mode : 3;
  int sign : 4;
  unsigned wide : 20;
};

unsigned
get_ready(struct flags *f) {
  return f->ready;
}
unsigned
get_mode(struct flags *f) {
  return f->mode;
}
int
get_sign(struct flags *f) {
  return f->sign;
}
unsigned
get_wide(struct flags *f) {
  return f->wide;
}

void
set_mode(struct flags *f, unsigned v) {
  f->mode = v;
}
void
set_sign(struct flags *f, int v) {
  f->sign = v;
}
void
set_wide(struct flags *f, unsigned v) {
  f->wide = v;
}

int
packed_sum(void) {
  struct flags f = {1, 5, -3, 1000};
  return f.ready + f.mode + f.sign + (int)f.wide;
}

/* The value of a bit-field assignment (§6.5.16.1) is the left operand after
   the store: the value truncated to the field width and re-extended per its
   signedness, not the raw right-hand side. */
unsigned
assign_value_unsigned(struct flags *f) {
  return (f->mode = 13); /* 13 = 0b1101; the 3-bit field holds 5 */
}
int
assign_value_signed(struct flags *f) {
  return (f->sign = 13); /* 13 = 0b1101; the signed 4-bit field is -3 */
}

/* The value of a compound assignment to a bit-field is likewise the stored
   (truncated) value (§6.5.16.1/.2), not the untruncated arithmetic result. */
unsigned
compound_value(struct flags *f) {
  f->mode = 6;
  return (f->mode += 5); /* 6 + 5 = 11 = 0b1011; the 3-bit field holds 3 */
}

/* A bit-field narrower than int promotes to int (§6.3.1.1), so comparing a
   negative value against an unsigned bit-field is a *signed* comparison:
   -1 < (any field value) is 1. An unsigned comparison would give 0. */
int
signed_compare(struct flags *f) {
  short s = -1;
  return s < f->mode;
}
