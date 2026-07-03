/* The parser resolves the C parameter-declaration ambiguity `T ( U ... )`.
   When U is a typedef name, C11 §6.7.6.3 ¶11 takes it as a *type*, so `(U)` is
   an abstract declarator (a function type) rather than a parenthesized
   declarator naming a parameter U. The three prototypes below elaborate to
   three distinct parameter types, pinning that the precedence resolution is
   both correct and selective. */

typedef int Num;

int takes_fp(int(Num));
int takes_ptr(int(*Num));
int takes_int(int(x));
