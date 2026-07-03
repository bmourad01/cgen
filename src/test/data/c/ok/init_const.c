typedef unsigned long bits;
enum { Pob = 3, Pbi1 = 5 };

/* §6.6: a cast to an integer typedef is a valid constant expression */
bits masks[] = {
  [4] = (bits)1 << Pob,
  [5] = (bits)1 << Pbi1,
  [6] = ((bits)1 << Pob) | ((bits)1 << Pbi1),
};

bits
mask_of(int n) {
  return masks[n];
}

/* §6.5.2.5: an array compound literal decays to a pointer to its first
   element; here it initializes a pointer at block scope. */
int
third(void) {
  int *p = (int[]){10, 20, 30};
  return p[2];
}

/* §6.5.2.5 ¶6: a compound literal outside any function has static storage,
   so its address is a constant */
typedef unsigned char uchar;
static uchar *matcher[] = {
  [1] = (uchar[]){1, 3, 1, 3, 2, 0},
  [2] = (uchar[]){9, 9, 9},
};

int
matcher_elt(int i, int j) {
  return matcher[i][j];
}
