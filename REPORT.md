# Programming Logic Report

## Environment
- OS: Ubuntu 24.04 (WSL)
- Editor: Antigravity, gvim
- OCaml version: 4.14.1
- Dune version: 3.22.0
- Tree-sitter version: 0.26.7
- Node version: 18.19.1
- NPM version: 9.2.0
- gcc version: 13.3.0
- g++ version: 13.3.0
- Make version: 4.3
- Z3 version: 4.15.2
- Machine: Intel Core i5-9400F 2.90GHz

## Software Setup
- Install Antigravity in Windows
- Install WSL (Ubuntu 24.04)
- Install Basic tools
~~~shell
sudo apt install -y build-essential pkg-config m4 curl git opam nodejs npm python3
sudo apt install vim
~~~

- Install Tree-sitter CLI
~~~shell
sudo npm install -g tree-sitter-cli
~~~

- OPAM initialization
~~~shell
opam init
# select "y" to update shell profile
~~~

- Install dune
~~~shell
opam install dune
~~~

- Git clone of the project (Personal Copy of the original project)
~~~shell
git clone https://github.com/KwangYungJeong/LogicVerify
~~~

- OPAM switch
~~~shell
opam switch create 4.14.1
opam switch set 4.14.1
# invrepair.export must be run in the project root directory
opam switch import invrepair.export
# This is just for editor (vim)
opam user-setup install
~~~

- Install Z3
~~~shell
sudo apt install z3
opam install z3
# I selected second method (opam install z3)
~~~

- Build
~~~shell
make clean
make
~~~
- Run
~~~shell
dune exec -- ./main.exe --input benchmarks/all.dfy
~~~

## Basic Check
