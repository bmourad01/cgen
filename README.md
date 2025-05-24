# Overview

cgen is a compiler backend.

Inspired by the [QBE](https://c9x.me/compile/) project.

# Setup

- To build and install the project, run `make` (these can be done individually with `make build` and `make install`, respectively).
- To uninstall the project, run `make uninstall`.
- To clean the build artifacts, run `make clean`.
- To run the unit tests, run `make test`.
- For generating documentation, run `make doc`.

The generated documentation (in HTML format) should be located in `./src/_build/default/_doc/_html/index.html`, which can be opened in your browser of choice.

# Usage

The basic usage is `cgen file.vir`, where `file.vir` is a file containing the syntax for cgen's user-facing intermediate language: "Virtual".
cgen will then transform the contents of this file, and the final output (via stdout) is an assembly program, which is intended to be fed into a common system assembler (such as GNU `as`).

See `cgen --help` for more information.

## Library

cgen is also intended to be used directly as a library for language front-ends.
The library API that is provided can be seen in the generated documentation.

# Pipeline

The compilation pipeline roughly follows this plan:

```
+---------------------------+
|    Virtual IR (input)     |
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual IR (SSA, parse,   |
| typecheck)                |
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual IR (mid-end       |
| optimizations)            |
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual ABI IR (ABI       |
| lowering)                 |
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual ABI IR (more      |
| optimizations)            |
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (instr.         |
| selection)                |
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (dead code      |
| elimination)              |
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (register       |
| allocation, stack layout) |
+-------------+-------------+
              |
              v
+---------------------------+
| Assembly (final output)   |
+---------------------------+
```
