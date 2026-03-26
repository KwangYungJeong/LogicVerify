# Project: Program Verifier

Implement a partial-correctness verifier in engine/verifier.ml and submit this file only. Do not add or modify other files. 

## Getting Started
```bash
# 1. Install the package dependencies
brew install opam tree-sitter node

# 2. Create a new opam switch and install the dependencies
opam switch create 4.14.2
opam switch set 4.14.2
opam import invrepair.export
```

## Build
```
make clean
make
```

## Run
```bash
dune exec -- ./main.exe --input benchmarks/all.dfy 
```