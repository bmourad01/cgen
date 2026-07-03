int
classify(int x) {
  switch (x) {
  case 0:
  case 1:
    return 1;
  case 2:
    return 2;
  default:
    return -1;
  }
}

int
days_in_month(int m) {
  int days;
  switch (m) {
  case 2:
    days = 28;
    break;
  case 4:
  case 6:
  case 9:
  case 11:
    days = 30;
    break;
  default:
    days = 31;
  }
  return days;
}

int
accumulate(int n) {
  int acc = 0;
  switch (n) {
  case 3:
    acc += 3;
  case 2:
    acc += 2;
  case 1:
    acc += 1;
  }
  return acc;
}
