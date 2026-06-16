# Ligare Language Design Document

> **Everything is a term. Everything is a constraint.**  
> File extension: `.lig`

[中文版](README_zh.md)

## 1. Core Philosophy

Ligare is a minimalist programming language. It recognizes only one kind of entity — the **Term**.  
There is no separate "type" syntax, no "type vs. value" dichotomy, and no "program vs. proof" dichotomy.  
Everything is a term, and every relationship is a **constraint**.

## 2. Terms and Constraints

### 2.1 Terms
A term is the only existence in the language. Variables, literals, functions, data types, propositions, proofs, macros... all are terms.

### 2.2 Constraints
Relationships between terms are established through **constraints**.  
`a constrained by T` means that term `a` belongs to term `T`.  
The constraint relationship replaces the "type ascription" found in traditional languages, but constraints themselves are also terms and can be constrained by other terms.

**Example**  
```
3 constrained by int
int constrained by data
```

### 2.3 Levels
All terms have a level. Constraint relationships enforce level ordering to prevent Russell-paradox-style self-referential structures.  
(Specific level rules will be defined in detail in the formalization section.)

### 2.4 Naming Conventions
- **Constraints / Types**: PascalCase (e.g., `Nat`, `Point`, `LinkedList`)
- **Functions / Theorems**: snake_case (e.g., `div`, `is_sorted`, `add_node`)

## 3. Meta-Constraints

The language has four built-in root constraints, called **meta-constraints**. They define the foundation of the universe.

| Meta-constraint | Meaning | Exists at runtime? |
|-----------------|---------|---------------------|
| `data` | The computable data universe; all terms ultimately retained belong here | Yes |
| `prop` | The proposition universe, describing logical conditions | No (erased) |
| `theorem` | An established proposition, encapsulating a proof | No (erased) |
| `proof` | The concrete construction of a proof; an evidence term | No (erased) |

All user-defined constraints are ultimately rooted beneath these four meta-constraints.

## 4. Refinement Constraints (Alias Constraints)

Users can define new constraints with attached propositional conditions. This is Ligare's way of defining "types."

**Syntax**  
```
constraint nat as (data x & x >= 0)
```

**Interpretation**  
`nat` is a new constraint. Any term constrained by `nat` must:
1. Be constrained by `data` (i.e., be computable data);
2. Carry a `proof` term demonstrating that the data satisfies `x >= 0`.

**Usage**  
```
a : nat   // a must be a non-negative integer
```
The compiler automatically demands this proof where needed, or derives it from context.

## 5. Functions and Contracts

Functions can constrain their own parameters and return values, forming pre/post-condition contracts.

**Syntax example**  
```
function div(a: int, b: int)
  param constraint: b ≠ 0
  output constraint: result * b = a
```

**Proof obligations**  
- The caller must provide a proof of `b ≠ 0` (or the compiler derives it automatically).
- The function body must construct the proof of `result * b = a`.

All proof terms (`proof`) are erased after passing compile-time checks, with zero runtime overhead.

## 6. `if` Expressions and Theorem Introduction

The condition of an `if` is treated as a proposition. When entering a branch, the branch context automatically introduces a corresponding `theorem`.

**Example**  
```
if (x > 0) then
  // a theorem: x > 0 is automatically available here
  // it can be used to satisfy proof obligations of other constraints
  div(10, x)  // x ≠ 0 can be automatically derived from x > 0
else
  // a theorem: not (x > 0) is automatically available here
```

After compilation, `if` is still compiled into a simple conditional jump; all proof parts are erased.

## 7. Structs

A struct is a compound term constrained by `data`, containing named fields and optional invariants.

**Definition example**  
```
constraint Point as data struct:
  field x : int
  field y : int
  invariant : x >= 0 ∧ y >= 0
```

**Construction**  
When constructing `Point`, a `proof` that the invariant holds must be provided.  
The compiler automatically generates:
- A constructor (with proof obligations)
- Field projection functions
- A `theorem` corresponding to the invariant (e.g., for any `p : Point`, `p.x >= 0` is an available theorem)

## 8. Compile-Time Metaprogramming

The `proof` universe also serves the role of metaprogramming.  
Any program used solely for generating `data` code can be written as a `proof` term, evaluated at compile time and spliced in.

**Mechanism**  
- Quote: converts a code fragment into manipulable AST data;
- Splice: inserts the AST produced by evaluating a `proof` term back into the `data` context.

**Safety guarantee**  
During splicing, the generated code is forcibly verified to satisfy the target constraint; otherwise compilation fails.

Since `proof` is ultimately erased, the metaprogramming parts never enter the runtime.

## 9. Compilation and Erasure

The compilation process is divided into two major phases:

1. **Constraint checking and proof verification**  
   Perform constraint checking on all terms and verify that all `proof` obligations are satisfied.

2. **Erasure and code generation**  
   Retain all terms constrained by `data`, and remove all terms constrained by `prop`, `theorem`, or `proof`.  
   The final product is pure, zero-overhead executable code.

## 10. Summary

Ligare uses the single core concept of **"terms constrained by terms"** to unify:
- The type system
- Propositions and proofs
- Design by contract
- Compile-time metaprogramming

It pursues **the extreme of static safety with zero runtime burden**, while maintaining a minimal set of concepts.  
This document is an outline of its core ideas; formal definitions, operational semantics, and implementation details will be added progressively.
