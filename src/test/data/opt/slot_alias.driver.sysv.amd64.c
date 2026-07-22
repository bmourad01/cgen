#include <assert.h>

struct t {
  signed f0;
  unsigned f1;
  unsigned : 10;
  unsigned f5 : 25;
  unsigned f6 : 9;
  unsigned f7 : 28;
  unsigned f8 : 6;
};

struct t tab[5][7];
int aux[5][8][1];

extern long run(void);

int
main() {
  long expect = 0;
  int i, j;

  for (i = 0; i < 5; i++) {
    for (j = 0; j < 7; j++) {
      unsigned n = (unsigned)(i * 7 + j + 1);
      tab[i][j].f0 = (signed)n;
      tab[i][j].f1 = n * 0x01010101u;
      tab[i][j].f5 = n * 7u;
      tab[i][j].f6 = n * 3u;
      tab[i][j].f7 = n * 11u;
      tab[i][j].f8 = n;
    }
  }

  for (i = 0; i < 5; i++) {
    for (j = 0; j < 7; j++) {
      expect += tab[i][j].f1;
      expect += tab[i][j].f5;
      expect += tab[i][j].f6;
      expect += tab[i][j].f7;
      expect += tab[i][j].f8;
    }
  }

  assert(run() == expect);
  return 0;
}
