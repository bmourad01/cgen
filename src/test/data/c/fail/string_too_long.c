/* Constraint violation (C99 6.7.8p14): the string literal has more
   characters than the array can hold; not even the no-NUL exception
   applies, since "abc" is 3 chars and the array holds 2. */
char buf[2] = "abc";
