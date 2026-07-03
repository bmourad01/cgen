#include <assert.h>

extern int land(int, int);
extern int lor(int, int);
extern int between(int, int, int);
extern int imax(int, int);
extern int iabs(int);
extern int clamp(int, int, int);
extern int is_alpha(int);
extern int is_leap(int);
extern int count_pos(const int *, int);
extern int first_is_pos(const int *, int);
extern int guarded(int, int (*)(void));
extern int max_if(int, int);
extern int sign_if(int);
extern int choose(int, int, int);
extern int count_pos_if(const int *, int);

static int calls = 0;
static int
bump(void) {
  calls += 1;
  return 7;
}

int
main(void) {
  assert(land(0, 5) == 0);
  assert(land(3, 5) == 1);
  assert(lor(0, 0) == 0);
  assert(lor(0, 9) == 1);
  assert(between(5, 1, 10) == 1);
  assert(between(0, 1, 10) == 0);
  assert(imax(3, 7) == 7);
  assert(imax(9, 2) == 9);
  assert(iabs(-4) == 4 && iabs(4) == 4);
  assert(clamp(5, 0, 10) == 5);
  assert(clamp(-3, 0, 10) == 0);
  assert(clamp(99, 0, 10) == 10);
  assert(is_alpha('q') && is_alpha('Z') && !is_alpha('0'));
  assert(is_leap(2000) && !is_leap(1900) && is_leap(2024) && !is_leap(2023));

  int xs[5] = {-1, 2, 0, 4, -5};
  assert(count_pos(xs, 5) == 2);
  assert(count_pos_if(xs, 5) == 2);
  assert(first_is_pos(xs, 5) == 0);
  int ys[2] = {3, 9};
  assert(first_is_pos(ys, 2) == 1);
  assert(first_is_pos((const int *)0, 0) == 0);

  calls = 0;
  assert(guarded(0, bump) == 0);
  assert(calls == 0);
  assert(guarded(1, bump) == 1);
  assert(calls == 1);

  assert(max_if(3, 7) == 7 && max_if(8, 1) == 8);
  assert(sign_if(5) == 1 && sign_if(-2) == -1 && sign_if(0) == 0);
  assert(choose(1, 10, 20) == 11);
  assert(choose(0, 10, 20) == 21);
  return 0;
}
