#include <stdio.h>

extern const char *const name;
extern void copy_str(char *dst, const char *src);

int
main() {
  char buf[64];
  copy_str(buf, "Hello, ");
  printf("%s%s\n", buf, name);
}
