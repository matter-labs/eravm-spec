# zkSync Era: Formal Specification of EraVM instruction set

[![Logo](eraLogo.svg)](https://zksync.io/)

zkSync Era is a layer 2 rollup that uses zero-knowledge proofs to scale Ethereum without compromising on security
or decentralization. As it's EVM-compatible (with Solidity/Vyper), 99% of Ethereum projects can redeploy without
needing to refactor or re-audit any code. zkSync Era also uses an LLVM-based compiler that will eventually enable
developers to write smart contracts in popular languages such as C++ and Rust.

This repository contains the formal specification for EraVM instruction set written in Coq, along with some artifacts generated from it.

## License

This library is distributed under the terms of either

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.


## Official Links

- [Website](https://zksync.io/)
- [GitHub](https://github.com/matter-labs)
- [Twitter](https://twitter.com/zksync)
- [Twitter for Devs](https://twitter.com/zkSyncDevs)
- [Discord](https://join.zksync.dev/)

## Disclaimer

zkSync Era has been through extensive testing and audits, and although it is live, it is still in alpha state and
will undergo further audits and bug bounty programs. We would love to hear our community's thoughts and suggestions
about it!
It's important to note that forking it now could potentially lead to missing important
security updates, critical features, and performance improvements.



# Setting up development environment

1. Install `make`.
2. Install Coq and required libraries:

  - `coq-ext-lib`
  - `coq-mathcomp-ssreflect`
  - `coq-record-update`

   We recommend [Opam](https://opam.ocaml.org/) (your packet manager probably has `opam` package).

   The following will pin the packages to specific versions that we are using at
   the time of development, preventing them from automatically updating via
   `opam upgrade`.

   ```
   opam pin add coq 8.17.0
   opam pin add coq-ext-lib 0.11.8
   opam pin add coq-mathcomp-ssreflect 1.17.0
   opam pin add coq-record-update 0.3.2
   ```

3. We consider the root directory of the project as the repository root.
   Execute this command in the project root:

   ```
   coq_makefile -f _CoqProject -o CoqMakefile
   ```

   This will create a file `CoqMakefile` for `make`.

# Build spec and proofs


```
make -f CoqMakefile -j<number of threads> all
```


# Generating docs

Generating docs is cumbersome to setup ATM because we use a custom script and a
custom version of `coqdoc` to fully support Markdown in documentation blocks.

1. Prepare the environment once
   - install Pandoc
   - install Python 3.6+
   - install `pypandoc` by executing `python3 -m pip install pypandoc`
   - clone and build `https://github.com/sayon/coq`
   - setup the variables in `build-docs.sh`
     + `COQDOC` -- point it to `coqdoc` that you have built from `https://github.com/sayon/coq`
       The executable should be located in `_build/install/default/bin/coqdoc` after successful build.
     + `COQLIB`. Put there the path to the directory with subdirectories `theories` and `user-contrib`. Usually `~/.opam/<ocaml-switch-name>/lib/coq/`.

2. Generate docs with `./build-docs.sh`
