# `lib/`

- **`cgen/`**
  - The core compiler backend
  - Contains all the algorithms, IRs, passes, interfaces, etc
- **`cgen-c/`**
  - A C99 frontend
- **`cgen-containers/`**
  - Internal library that implements various specialized container data structures.
  - These data structures are used internally but not directly exposed via `cgen`'s API
  - Not for public consumption
- **`cgen-utils/`**
  - Miscellaneous helper modules that are shared across other cgen libraries
