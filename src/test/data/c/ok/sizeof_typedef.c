/* `sizeof` applied to a typedef-name must resolve the typedef to its
   underlying type before computing the size (§6.5.3.4). A real
   `#include <stdio.h>` depends on this: glibc's `struct _IO_FILE` sizes an
   array with `sizeof(size_t)`, so getting this wrong makes the header
   unusable ("unresolved typedef"). */

typedef unsigned long my_size_t;
typedef int *my_intptr;

/* The glibc `struct _IO_FILE` pattern: a typedef-name inside a constant
   array dimension. */
struct padded {
  char used[4];
  char pad[32 - 4 - sizeof(my_size_t)];
};

unsigned long
size_of_typedef(void) {
  return sizeof(my_size_t);
}

unsigned long
size_of_pointer_typedef(void) {
  return sizeof(my_intptr);
}

unsigned long
size_of_padded_struct(void) {
  return sizeof(struct padded);
}
