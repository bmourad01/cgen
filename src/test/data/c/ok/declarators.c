int *ap[3];
int (*pa)[3];
int (*fp)(int, int);
int (*fps[5])(int);
const int *const cp;
char *const *p;

/* C99 array parameter declarators: type qualifiers and `static` inside the
   brackets (§6.7.6.2). */
void arr_restrict(int a[restrict]);
int arr_static(int a[static 4]);
void arr_const(char c[const]);
int arr_static_quals(const int a[const static 8]);
