#include <assert.h>
#include <stdbool.h>

bool palindrome(int n);

int
main() {
  assert(palindrome(0));
  assert(palindrome(1));
  assert(palindrome(12321));
  assert(!palindrome(1234));
  assert(palindrome(-1));
  assert(palindrome(-11));
  assert(palindrome(-121));
  assert(palindrome(-12321));
  assert(!palindrome(-12));
  assert(!palindrome(-1234));
  assert(!palindrome(-10));
}
