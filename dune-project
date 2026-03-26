(lang dune 2.4)

(using menhir 2.1)

(name pronto)

(package
  (name pronto)
  (depends
    (dune :build)
    (menhir :build)
    (core :build)
    (z3 :build)))