# Red-Black Tree: A Synthesis of Algorithm, Logic, and Ontology

This repository provides an implementation of the Red-Black Tree data structure as defined in *Introduction to Algorithms* (CLRS, Chapter 13).

However, rather than a mere procedural translation, this codebase is structured around a rigorous philosophical and mathematical framework. It demonstrates how to program by unifying three distinct paradigms: **Ontology**, **Mathematical Logic**, and **Algorithm**.

## The Three Pillars of this Implementation

### 1. Ontology (The Domain Model)
*Defines WHAT exists and HOW concepts relate.*
We utilize Lisp structs, contracts, and type hierarchies to build a formal domain model. This establishes the strict universe of discourse before any computation occurs. A node is not just memory; it is an entity bound by formal structural relations.

### 2. Logic (The Invariants)
*Defines WHAT MUST BE TRUE at all times.*
The mathematical properties of the Red-Black tree are not left to chance or implicit assumption; they are codified as executable predicates and contracts.

### 3. Algorithm (The Procedures)
*Defines HOW to compute while preserving truth.*
With the Ontology defining the space and the Logic defining the boundaries, the algorithms from CLRS act as the dynamic engine. They mutate the state of the tree while mathematically guaranteeing that no logical invariants are violated.

---

## Environment & Usage

This implementation is written in Racket and designed to be executed within **DrRacket**.

1. Open the `.rkt` (or `.lisp`) file in DrRacket.
2. Ensure the language directive at the top of the file is correct (e.g., `#lang racket`).
3. Click **Run** to load the definitions and enforce the logical contracts.
4. In the interactions area (REPL) at the bottom, you can test the algorithm and observe the invariants holding true:

```racket
;; Example REPL interaction
(define test-tree (make-rb-tree))
(rb-insert! test-tree 42)
(rb-insert! test-tree 15)
;; The tree automatically balances and recolors while preserving the Red-Black axioms.
