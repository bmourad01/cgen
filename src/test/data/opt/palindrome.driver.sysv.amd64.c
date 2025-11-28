#include <assert.h>
#include <stdbool.h>

bool palindrome(int n);

int
main() {
  assert(palindrome(0));
  assert(palindrome(1));
  assert(palindrome(12321));
  assert(!palindrome(1234));
}
