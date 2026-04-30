# `lib/`

- **`cgen/`**
  - The core compiler backend
  - Contains all the algorithms, IRs, passes, interfaces, etc
- **`cgen-containers/`**
  - Internal library that implements various specialized container data structures.
  - These data structures are used internally but not directly exposed via `cgen`'s API
  - Not for public consumption
