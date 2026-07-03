#include <assert.h>

extern unsigned f_a(void);
extern unsigned f_b(void);
extern int f_c(void);
extern int f_x(void);
extern int m_p(void);
extern int m_q(void);
extern unsigned m_r(void);

int
main(void) {
  assert(f_a() == 5);
  assert(f_b() == 20);
  assert(f_c() == -2);
  assert(f_x() == 0x1234);
  assert(m_p() == -100);
  assert(m_q() == 300);
  assert(m_r() == 1);
  return 0;
}
