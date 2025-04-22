# (Maybe Complete) Classical-Quantum Relational Hoare Logics

This is the project repository for cqotl.

GitHub repository: https://github.com/LucianoXu/cqotl.git

## Structure
- `generator`: the verification condition generator in OCaml
- `lean-veri`: the formalization of theories for verification conditions in Lean

## Setup & Installation

### Running the Dune Project in `generator/`

#### Prerequisites
- **OCaml** (version 4.12.0 or later recommended)
- **Dune** (version 2.9.0 or later)
- **opam** (for dependency management)
- **Menhir** (version 3.0 or later)
#### Setup and Execution

1. Navigate to the `generator` directory:
   ```bash
   cd generator
   ```

2. Install dependencies:
    ```bash
    opam install . --deps-only
    ```

3. Build and run:
    ```bash
    dune build && dune exec ./bin/main.exe
    ```

## Tasks to be completed:

### Generator

- [ ] Implementation of qWhile
    - [x] Parsing, AST, and Pretty Printing Added
    - [ ] qWhile examples
    - [ ] assertiong language
    - [ ] (maybe) semantics

- [ ] REPL
    - [x] Basic command line REPL
    - [ ] Solve the parsing conflicts (see _build/default/lib/parser.conflicts)
    - [ ] REPL context
    - [ ] Pretty-printing


### Coq Formalization in `coq_formal/`

This folder contains the Coq formalization of this project.

#### Prerequisites
- **Coq Proof Assistant, version 8.20+** (including `coqc` and `coq_makefile`)

#### Setup & Installation

1. Generate a `Makefile`.
```bash
coq_makefile -f _CoqProject -o Makefile
```

2. Compile the `.v` files
```bash
make
```