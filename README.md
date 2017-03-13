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

(* show dependencies for constants *)
Depends Fin.fin_eq_dec Fin.all_fin.

(* write dependencies to file for constants *)
Depends "fin-deps.dep" Fin.fin_eq_dec Fin.all_fin.

(* show dependencies for the types of constants *)
TypeDepends Fin.fin_eq_dec Fin.all_fin_all.

(* write dependencies to file for the type of constants *)
TypeDepends "fin-type-deps.txt" Fin.fin_eq_dec Fin.all_fin_all.

(* show dependencies of all constants in given modules *)
ModuleDepends Fin RemoveAll.

(* write dependencies to file for all constants in given modules *)
ModuleDepends "fin-removeall-deps.txt" Fin RemoveAll.

(* show type dependencies of all constants in given modules *)
ModuleTypeDepends Fin RemoveAll.

(* write dependencies to file for all types of constants in given modules *)
ModuleTypeDepends "fin-removeall-type-deps.txt" Fin RemoveAll.
```
