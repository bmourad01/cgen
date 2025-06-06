# Overview

cgen is a compiler backend.

Inspired by the [QBE](https://c9x.me/compile/) project.

# Setup

- To install the opam dependencies, run `make deps`
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

There are three IRs used by the compiler:

1. **Virtual**: CFG-based, platform-agnostic intermetiate language. Similar to LLVM IR, but smaller in scale.
2. **Virtual ABI**: almost the same as Virtual, but with explicit mentioning of registers, stack locations,
   and with platform-specific instructions (such as `va_arg` and `va_start`) desugared, and with the target
   ABI implemented for function calling.
3. **Pseudo**: "pseudo"-assembly, CFG-based representation with concrete, target-specific instructions. This
   is generated at instruction selection time. Maintains the stack slot abstraction up until register allocation.

The compilation pipeline roughly follows this plan:

```
+---------------------------+
|    Virtual IR (input)     | Input can be parsed from textual representation, or constructed in-memory.
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual IR (SSA, type     | Transform to semi-pruned SSA form, type check the module.
| checking)                 |
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual IR (mid-end       | Control-flow simplifications, algebraic rewrites, constant propagation,
| optimizations)            | constant folding, GVN, GCM, LICM, RLE, store-to-load forwarding, etc.
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual ABI IR (ABI       | Remove aggregate types, implement the platform-specific rules for parameter
| lowering)                 | passing and returning values from functions via registers/stack, etc.
+-------------+-------------+
              |
              v
+---------------------------+
| Virtual ABI IR (more      | CSE, RLE, store-to-load forwarding, etc.
| optimizations)            | 
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (instr.         | Implements a greedy, maximal-munch algorithm to match tree patterns over a
| selection)                | DAG of the function.
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (dead code      | Eliminates dead code generated by the previous pass.
| elimination)              |
+-------------+-------------+
              |
              v
+---------------------------+
| Pseudo IR (register       | Implements the Iterated Register Coalescing (IRC) algorithm.
| allocation, stack layout) |
+-------------+-------------+
              |
              v
+---------------------------+
| Assembly (final output)   | Platform-specific assembly code.
+---------------------------+
```
