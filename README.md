coq-depends
===========

A Coq plugin for non-recursive extraction of dependencies of terms, derived from [coq-dpdgraph](https://github.com/Karmaki/coq-dpdgraph).

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/coq-85)

Installation
------------

The easiest way to install coq-depends is via OPAM:

```
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install coq-depends
```

Usage
-----

```coq
(* modules to analyze; do not import! *)
Require StructTact.Fin.
Require StructTact.RemoveAll.

(* load plugin *)
Require Import Depends.Depends.

(* show dependencies for single constant *)
Depends Fin.fin_eq_dec.

(* show dependencies for the type of a constant *)
TypeDepends Fin.all_fin_all.

(* show dependencies of all constants in given modules *)
ModuleDepends Fin RemoveAll.
```
