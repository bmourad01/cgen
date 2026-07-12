/* C11 alignment specifier (§6.7.5): `_Alignas`/`alignas` with a constant
   or a type-name, on globals, block-scope statics, and locals. Modeled as
   an `aligned` attribute. */

_Alignas(32) long g32[4] = {1, 2, 3, 4};
alignas(16) char cbuf[8];
_Alignas(double) char adbl;

int
local_aligned(void) {
  alignas(16) int a[4];
  static _Alignas(16) char s[8];
  a[0] = 5;
  s[0] = 6;
  return ((unsigned long)a % 16 == 0 && (unsigned long)s % 16 == 0)
           ? a[0] + s[0]
           : 0;
}
