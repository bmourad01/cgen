/* Integer-literal typing per C99 §6.4.4.1 ¶5: a decimal constant's
   candidate types are signed, but an octal, hexadecimal, or binary
   constant also admits the unsigned variant of each rank. Binary
   literals are a GCC/Clang extension (standard since C23). */

long
hex_uint_wrap(void) {
  return 0xFFFFFFFF + 1;
}

long
dec_long_nowrap(void) {
  return 4294967295 + 1;
}

int
hex_ull_is_unsigned(void) {
  return 0xFFFFFFFFFFFFFFFF > 0;
}

int
oct_value(void) {
  return 010 + 0777;
}

int
bin_value(void) {
  return 0b1011 + 0B100;
}
