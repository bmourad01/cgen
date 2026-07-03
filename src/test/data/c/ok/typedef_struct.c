typedef unsigned long size_t;

typedef struct point {
  int x;
  int y;
} point;

struct rect {
  point lo;
  point hi;
  unsigned char flags : 3;
};

size_t count;
point origin;
struct rect bounds;
