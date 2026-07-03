int
next_id(void) {
  static int counter = 0;
  counter = counter + 1;
  return counter;
}

int
next_seq(void) {
  static int counter = 100;
  counter = counter + 1;
  return counter;
}

char
greeting_char(int i) {
  static const char msg[] = "hi";
  return msg[i];
}

int
squares(int n) {
  int total = 0;
  for (int i = 0; i < n; i = i + 1) {
    static int base = 2 * 5;
    total = total + base + i;
  }
  return total;
}

int shared = 7;

int
get_shared(void) {
  extern int shared;
  return shared;
}
