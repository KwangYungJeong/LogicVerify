# Project: Program Verifier (Linux / Ubuntu)

This document explains how to set up and run this project on Ubuntu.

## Prerequisites

Ubuntu packages (adjust versions if your distro differs):

```bash
sudo apt update
sudo apt install -y \
  build-essential \
  pkg-config \
  m4 \
  curl \
  git \
  opam \
  nodejs npm \
  python3
```

Z3 is used by the OCaml `z3` binding. This guide installs Z3 **from the Git repository** (libraries + headers for linking). See [Z3 from source](#z3-from-git-build-and-install) below—do that **before** `opam switch import` / `opam install` so the `z3` OCaml package can find `libz3`.

Some setups also require a compiler toolchain for OCaml dependencies:

```bash
sudo apt install -y gcc g++
```

tree-sitter CLI (used by parts of the toolchain):

```bash
sudo npm install -g tree-sitter-cli
```

### Z3 from Git (build and install)

Z3’s usual flow from a clone is: **Python configure script → `make` in `build/` → `sudo make install`**. (Upstream also supports CMake; this guide sticks to the classic path.)

Clone the default branch (or any revision you choose), then:

```bash
git clone https://github.com/Z3Prover/z3.git
cd z3
python3 scripts/mk_make.py
cd build
make
sudo make install
sudo ldconfig
```

**Note — why `sudo ldconfig` after `make install`:**  
`make install` puts shared libraries (e.g. `libz3.so`) under paths like `/usr/local/lib`. The dynamic linker uses `/etc/ld.so.cache` to resolve `.so` files system-wide. `ldconfig` refreshes that cache so newly installed libraries are found reliably. If you skip it, you may still succeed depending on RPATH, `LD_LIBRARY_PATH`, or prior cache state—but it is common to see runtime errors such as *cannot open shared object file: libz3.so* right after a fresh install. Running `sudo ldconfig` once after install is the usual safe habit.

If you want a fixed Z3 revision for reproducibility, check out a tag or commit **before** `mk_make.py` (see [Z3 releases](https://github.com/Z3Prover/z3/releases)); this guide does not require a particular version.

To install under a specific prefix (e.g. `/usr/local`, often the default for `make install`):

```bash
python3 scripts/mk_make.py --prefix=/usr/local
```

If the OCaml `z3` package later fails to find Z3 via pkg-config, try (then retry `opam install z3` in a **new** shell after Z3 install):

```bash
export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig:${PKG_CONFIG_PATH}
```

## 1) Initialize opam (first time only)

If you have never run opam on this machine, create its root and default configuration **once**:

```bash
opam init
```

**Shell profile:** when `opam init` asks whether to update your shell startup file (**`~/.profile`**, **`~/.bashrc`**, or **`~/.zshrc`** depending on your shell), answer **yes**. That wires opam so new terminals load the active switch (equivalent to running `eval $(opam env)` automatically). Then either open a new terminal or run `source ~/.bashrc` (or the file opam modified).

If you already ran `opam init` and skipped that step, add the hook yourself, e.g. for Bash:

```bash
grep -q 'opam env' ~/.bashrc || echo 'eval $(opam env)' >> ~/.bashrc
```

For Zsh, use `~/.zshrc` instead. For login-only shells, some setups use `~/.profile`.

In CI, Docker, or some VMs where the sandbox fails:

```bash
opam init --disable-sandboxing
```

Still accept **yes** to shell profile updates when prompted (or add `eval $(opam env)` manually as above). Non-interactive `-y` may skip questions; if `dune` is missing in new shells, verify the profile hook or run `eval $(opam env)` once per session.

If `~/.opam` already exists and `opam switch list` works, you can skip `opam init`.

## 2) Create an opam switch (OCaml version)

This repository expects OCaml 4.14.2 (see `invrepair.export`).

From the project root:

```bash
opam switch create 4.14.2
opam switch set 4.14.2
opam switch import invrepair.export
```

**Note:** `opam import` exists only in **opam 2.1+**. Ubuntu’s `apt` package is often **opam 2.0.x**, which has no top-level `import`; use **`opam switch import invrepair.export`** instead (as above). With opam 2.1+, `opam import invrepair.export` is an alias-style shortcut you can use if available.


Apply the opam environment to your current shell:

```bash
eval $(opam env)
```

### OCaml `z3` binding (required; not in `invrepair.export`)

`dune` reports `Library "z3" not found` when the **opam package** `z3` is missing. That is separate from building Z3 from Git: you need the C library installed first (see [Z3 from Git](#z3-from-git-build-and-install)), then install the OCaml bindings:

```bash
eval $(opam env)
opam install z3
```

`invrepair.export` does **not** list `z3`, so `opam switch import` alone will not install it. If `opam install z3` fails to find native Z3, set `PKG_CONFIG_PATH` as in the Z3 section and retry.

## 3) Build

```bash
make clean
make
```

If you still get `dune: No such file or directory`, re-run:

```bash
eval $(opam env)
```

Optionally (rarely needed if `invrepair.export` installed it already):

```bash
opam install dune
```

## 4) Run the verifier

The verifier is invoked by `main.exe` and reads the Dafny programs from `--input`.

```bash
dune exec -- ./main.exe --input benchmarks/all.dfy
```

## Notes / Troubleshooting

### `make: dune: No such file or directory`

Usually means the current terminal is not using the opam switch environment.

Run:

```bash
eval $(opam env)
make
```

### Why not `apt install ocaml-dune`?

This repo is designed around the opam switch. Installing `dune` via `apt` can lead to PATH/version mismatches. Prefer `opam install dune` (or rely on `invrepair.export`) after `eval $(opam env)`.

