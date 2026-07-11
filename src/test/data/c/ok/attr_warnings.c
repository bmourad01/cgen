__attribute__((deprecated)) int old_fn(void);
__attribute__((deprecated("use new_count instead"))) int old_count;
__attribute__((warn_unused_result)) int checked(void);

int new_count;

int
call_old(void) {
  return old_fn();
}

int
read_old(void) {
  return old_count;
}

void
drop_result(void) {
  checked();
}

int
keep_result(void) {
  int x = checked();
  return x;
}

void
void_cast(void) {
  (void)checked();
}
