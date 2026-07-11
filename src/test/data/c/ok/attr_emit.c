int weak_var __attribute__((weak)) = 7;

int in_section __attribute__((section(".mydata"))) = 3;

__attribute__((visibility("hidden"))) int hidden_var = 1;

__attribute__((weak)) int
weak_fn(void) {
  return 42;
}

__attribute__((visibility("hidden"))) int
hidden_fn(void) {
  return hidden_var;
}

__attribute__((visibility("protected"))) int
protected_fn(void) {
  return 1;
}
