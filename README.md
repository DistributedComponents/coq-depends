Depends Coq Plugin
==================

[![Build Status](https://api.travis-ci.org/proofengineering/coq-depends.svg?branch=master)](https://travis-ci.org/proofengineering/coq-depends)

A Coq plugin for non-recursive extraction of dependencies of terms, derived from [coq-dpdgraph](https://github.com/Karmaki/coq-dpdgraph).

Requirements
------------

- [`Coq 8.5`](https://coq.inria.fr/coq-85)
- ['camlp5'](https://camlp5.github.io)

Installation
------------

The easiest way to install the plugin is via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add proofengineering-dev http://opam-dev.proofengineering.org
opam install coq-depends
```

To build the plugin manually, run `make` in the root directory. Then, to install it, run `make install`.

Usage Examples
--------------

```coq
Require Import Depends.Depends.

(* print dependencies as JSON for constants *)
Depends List.map List.filter.

(* write dependencies to file as JSON for constants *)
Depends "deps.json" List.map List.filter.

(* show dependencies as JSON for the types of constants *)
TypeDepends List.map List.filter.

(* write dependencies to file as JSON for the type of constants *)
TypeDepends "typedeps.json" List.map List.filter.

(* show dependencies as JSON of all constants in given modules *)
ModuleDepends Logic List.

(* write dependencies as JSON to file for all constants in given modules *)
ModuleDepends "deps.json" Logic List.
```
