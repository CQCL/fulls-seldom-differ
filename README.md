# Supplementary Material for *Fulls Seldom Differ*

This repository contains supplementary material for our 2025 ICFP paper *Fulls Seldom Differ*.


## Fulbourn Language Implementation and Examples

The Haskell implementation of our toy language Fulbourn is available in the `fulbourn` directory.

To run the files in this directory, a haskell installation with a GHC version of at least 9.6.6 is required.

Fulbourn programs can be type-checked by running
```sh
cd fulbourn
runhaskell Main.hs --check [files]
```
Example Fulbourn programs (including the Batcher's even-odd merge sort example from the paper) are
available in the `fulbourn/examples` subdirectory. They can be checked by running (for example)
`runhaskell Main.hs --check examples/arith.txt`.

Programs can also be elaborated, using `runhaskell Main.hs --elab [file]`, which will print the file
to the terminal with omitted number patterns solved.

To run a Fulbourn program, it must contain a constant named `main`.
Running `runhaskell Main.hs --run [files]` will print the the value of `main` to the terminal.
See `examples/main.txt` for an example that runs Batcher's even-odd merge sort.

All of the Fulbourn code examples in the paper can be found in either `fulbourn/examples/arith.txt` or in `fulbourn/examples/examples.txt`.

Correctness tests of the sorting algorithm and other functions are in the file `Test.hs`, which can be run with `runhaskell Main.hs --test`.


## Formalisation of Theorem 6.3

A machine checked proof of Theorem 6.3 in Agda can be found in `normalisation/Norm.agda`, under the name `thm`.
To check the proof, run `agda normalisation/Norm.agda`.

This has been tested with agda version 2.6.4.3

## Formalisation of Sections 7 and 8

We also provide an Agda formalisation of our pullback arguments in Section 7 and 8, including a
proof of Theorem 8.5 in the `completeness` directory, under `TermQuad.agda`.
To check the proof, run `agda completeness/TermQuad.agda`.


## Formalisation of Section 10

An implementation of the `nunify` algorithm from Section 10 in Rocq/Coq (including the termination
proof) is available in `unify/solver.v`.

The file was tested with Coq version 8.18.0. The `nunify_fast` function and the end of the file furthermore requires the [`Equations`](https://mattam82.github.io/Coq-Equations/) package which can be install via `opam install coq-equations`.

To check the proof, run
```sh
cd ~/artefact/unify
make validate
```
Which should produce the following output
```
CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Axioms:
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep

* Constants/Inductives relying on type-in-type: <none>

* Constants/Inductives relying on unsafe (co)fixpoints: <none>

* Inductives whose positivity is assumed: <none>
```
The only assumed axiom is dependent functional extensionality arising from the use of the `Equations` package to define the alternative `nunify_fast` function.
