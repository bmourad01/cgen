int
target_fn(int x) {
  return x + 100;
}

int aliased_fn(int x) __attribute__((alias("target_fn")));

int the_answer = 42;

extern int aliased_var __attribute__((alias("the_answer")));
