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
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install coq-depends
```

Usage
-----

```coq
(* modules to analyze, do not import *)
Require StructTact.Fin.
Require StructTact.RemoveAll.

(* load plugin *)
Require Import Depends.Depends.

(* dependencies for single constant *)
Depends Fin.fin_eq_dec.

(* dependencies of the type of the constant *)
TypeDepends Fin.all_fin_all.

(* dependencies of all constants in given modules *)
ModuleDepends Fin RemoveAll.
```
