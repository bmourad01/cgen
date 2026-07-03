typedef struct opaque opaque_t;

int
is_null(opaque_t *p) {
  return p == 0;
}

struct b_node;
struct a_node {
  int va;
  struct b_node *b;
};
struct b_node {
  int vb;
  struct a_node *a;
};

int
cross(struct a_node *x) {
  return x->va + x->b->vb + x->b->a->va;
}

typedef struct list_node node_t;
struct list_node {
  int v;
  node_t *next;
};

int
sum(node_t *n) {
  int s = 0;
  while (n) {
    s += n->v;
    n = n->next;
  }
  return s;
}
