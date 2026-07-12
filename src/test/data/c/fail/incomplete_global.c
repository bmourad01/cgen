/* A file-scope tentative definition (§6.9.2) whose type is never completed
   is an error at the end of the translation unit. */
struct S;
struct S x;
