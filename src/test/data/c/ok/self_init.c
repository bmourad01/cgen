/* §6.2.1 ¶7: a declared identifier's scope begins just after its declarator,
   before its initializer, so an object may refer to itself (its own address)
   in its own initializer. The initializer must still complete an inferred
   array bound. */

struct list {
  struct list *next, *prev;
};

int
selfref(void) {
  struct list r = {&r, &r};
  return r.next == &r && r.prev == &r;
}

unsigned long
array_size(void) {
  int a[] = {1, 2, 3, 4, 5};
  return sizeof a;
}
int
array_sum(void) {
  int a[] = {10, 20, 30};
  return a[0] + a[1] + a[2];
}

int
self_pointer(void) {
  int x = 7;
  int *p[] = {&x, &x, &x};
  return *p[0] + *p[1] + *p[2];
}
