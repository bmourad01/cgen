#include <assert.h>
#include <stdint.h>

extern int8_t g_b;
extern int16_t g_h;
extern int32_t g_w;
extern int64_t g_l;
extern int64_t g_big;

extern void set_b(void);
extern void set_h(void);
extern void set_w(void);
extern void set_l(void);
extern void set_big(void);

int
main(void) {
  set_b();
  set_h();
  set_w();
  set_l();
  set_big();
  assert(g_b == 0x12);
  assert(g_h == 0x1234);
  assert(g_w == 0x12345678);
  assert(g_l == 0x7fffffff);
  assert(g_big == 0x123456789LL);
  return 0;
}
