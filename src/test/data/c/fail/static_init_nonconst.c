/* C99 6.7.8p4: an object with static storage duration must be
   initialized by a constant expression. Reading another object is not
   constant, so the initializer of g is rejected, with the diagnostic
   anchored at the offending expression rather than the declaration. */
int x;
int g = x;
