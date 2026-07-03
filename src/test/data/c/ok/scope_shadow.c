/* A block-scope declaration shadows an outer object (a global, or an enclosing
   local) only within its block; references after the block resolve to the outer
   object again (§6.2.1). */

int g = 7;

int
after_block(void) {
  int r;
  {
    int g = 99;
    r = g;
  }
  return r + g; /* 99 (inner) + 7 (global) */
}

int
nested(void) {
  int x = 1;
  {
    int x = 2;
    {
      int x = 3;
      if (x != 3)
        return -1;
    }
    if (x != 2)
      return -2;
  }
  return x;
}

int
for_shadow(void) {
  int sum = 0;
  for (int g = 0; g < 5; ++g)
    sum += g;
  return sum + g; /* 10 (loop sum) + 7 (global) */
}
