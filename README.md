# Specification for zkEVM

This is an effort to formalize zkEVM in Coq.

## What is Coq?

Coq is a proof assistant incorporating the functional programming language with the same name.
This language has a rich type system capable of encoding statements of logic (this is called Curry-Howard isomorphism).
Such a language can be used to:

- encode logical statements
- encode their proofs and automatically verify their correctness
- encode arbitrary finite computations (`while (true) {}` is forbidden, the language is therefore not Turing-complete).

Additionally, Coq as a proof assistant can:

- facilitate the proof construction through a limited proof search
- modularize descriptions of computation and proof in different ways
- extract the computations from Coq to Ocaml. Therefore one way of verifying programs is writing them in Coq, proving their properties, letting Coq verify these proofs, and automatically extracting a compilable Ocaml code.


Coq as a functional language is rich in functionality and you can extend it in a variety of ways.
We use one such extension providing a [nicer syntax to set fields of records](https://github.com/tchajed/coq-record-ui pdate)

However, the core language stays small, and everything else builds on top of it.
Therefore language extensions do not compromise the robustness of the proof checking.

Coq is written in Ocaml and enjoys integration with its ecosystem.


As `int` is a type of an object corresponding to any integer number, `int->int` is a type of an object corresponding to any function from `int` to `int`, `forall i, exists k, k = i + 1` is a type of any *proof* of the fact, encoded in the type.


#  How to build

## Set up the environment
1. install [Opam](https://opam.ocaml.org/) (your packet manager probably has it).
2. install Coq using `opam pin add coq 8.17.0`. This will install Coq version 8.17.0 instead of the latest available version; if a newer version of Coq appears, it will be skipped.
3. install https://github.com/tchajed/coq-record-update
4. to generate docs:
    - install Pandoc
    - install Python 3.6+
    - install `pypandoc` by executing `python3 -m pip install pypandoc`

## Build

We consider the root directory of the project the repository root, holding the folder `src` and the file `_CoqProject`.
Navigate there and execute:

1. `coq_makefile -f _CoqProject -o CoqMakefile` will create a file `CoqMakefile` for `make`. This should be done once.
2. To build specs and proofs: `make -f CoqMakefile -j<number of threads> all`
3. To generate docs: `./build-docs.sh`. Recreates `doc` directory on each invokation.
