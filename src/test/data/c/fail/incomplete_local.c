/* A block-scope object must have a complete type (§6.7 ¶7); an incomplete
   (forward-declared) struct cannot be used by value. */
struct S;

int
f(void) {
  struct S x;
  return sizeof x;
}
