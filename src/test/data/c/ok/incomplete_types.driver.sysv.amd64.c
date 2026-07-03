#include <assert.h>

typedef struct opaque opaque_t;
struct b_node;
struct a_node {
  int va;
  struct b_node *b;
};
struct b_node {
  int vb;
  struct a_node *a;
};
struct list_node {
  int v;
  struct list_node *next;
};

extern int is_null(opaque_t *p);
extern int cross(struct a_node *x);
extern int sum(struct list_node *n);

int
main(void) {
  assert(is_null(0) == 1);
  assert(is_null((opaque_t *)1) == 0);

  struct a_node a2 = {100, 0};
  struct b_node b = {20, &a2};
  struct a_node a1 = {1, &b};
  assert(cross(&a1) == 1 + 20 + 100);

  struct list_node n3 = {3, 0};
  struct list_node n2 = {2, &n3};
  struct list_node n1 = {1, &n2};
  assert(sum(&n1) == 6);

  return 0;
}
