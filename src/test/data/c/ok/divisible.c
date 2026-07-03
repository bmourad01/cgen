int
s_div3(int x) {
  return x % 3 == 0;
}

int
s_div4(int x) {
  return x % 4 == 0;
}

int
s_div100(int x) {
  return x % 100 == 0;
}

int
s_ndiv7(int x) {
  return x % 7 != 0;
}

unsigned
u_div6(unsigned x) {
  return x % 6 == 0;
}

unsigned
u_div10(unsigned x) {
  return x % 10 == 0;
}

unsigned
u_mod7(unsigned x) {
  return x % 7;
}

unsigned
u_mod641(unsigned x) {
  return x % 641;
}
