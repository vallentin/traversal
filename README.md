# traversal

[![Build Status](https://github.com/vallentin/traversal/workflows/Rust/badge.svg)](https://github.com/vallentin/traversal/actions?query=workflow%3ARust)
[![Build Status](https://travis-ci.org/vallentin/traversal.svg?branch=master)](https://travis-ci.org/vallentin/traversal)
[![Latest Version](https://img.shields.io/crates/v/traversal.svg)](https://crates.io/crates/traversal)
[![Docs](https://docs.rs/traversal/badge.svg)](https://docs.rs/traversal)
[![License](https://img.shields.io/github/license/vallentin/traversal.svg)](https://github.com/vallentin/traversal)

Traversal implements generic and lazy tree traversal algorithms.

Includes:
- [Breadth-First Traversal] ([`Bft`])
- [Depth-First Traversal] in Pre-Order ([`DftPre`])
- [Depth-First Traversal] in Post-Order ([`DftPost`])
- Reverse [Depth-First Traversal] in Pre-Order ([`DftPreRev`])
- Reverse [Depth-First Traversal] in Post-Order ([`DftPostRev`])
<!---->
- All Paths ([`DftPaths`])
- Longest Paths ([`DftLongestPaths`])
- All Cycles (Paths) ([`DftCycles`])

[Breadth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
[Depth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal

### Generic

Traversal uses [generics] (or [type parameters]) to be
flexible to use, and easy to implement and fit into existing
architecture.

[generics]: https://doc.rust-lang.org/rust-by-example/generics.html
[type parameters]: https://doc.rust-lang.org/reference/types/parameters.html

### Laziness

Laziness or [lazy evaluation] refers to evaluation being delayed
until needed.

Traversal delays processing `Node`s and fetching child `Node`s
until [`Iterator::next`][`next`] is called.
When [`next`] is called, then traversal only processes the
`Node`s required for this iteration.

[lazy evaluation]: https://en.wikipedia.org/wiki/Lazy_evaluation

*From Rust's docs:*

> *Iterators (and iterator [adapters]) are lazy. This means that just
> creating an iterator doesn't do a whole lot. Nothing really happens
> until you call [`next`].*
>
> &mdash; [`Iterator`] - [Laziness]

[`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
[`next`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#tymethod.next

[Laziness]: https://doc.rust-lang.org/std/iter/index.html#laziness
[adapters]: https://doc.rust-lang.org/std/iter/index.html#adapters

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
traversal = "0.1"
```

## Releases

Release notes are available in the repo at [CHANGELOG.md].

[CHANGELOG.md]: CHANGELOG.md

## Algorithms

```text
     A
    / \
   B   C
  / \ / \
 D  E F  G
```

Given the above tree, then the following are the orders,
that each individual iterator / traversal algorithm produces.

| Algorithm | Order |
|-----------|-------|
| [`Bft`]        (Breadth-First Traversal)                     | A, B, C, D, E, F, G |
| [`DftPre`]     (Depth-First Traversal in Pre-Order)          | A, B, D, E, C, F, G |
| [`DftPost`]    (Depth-First Traversal in Post-Order)         | D, E, B, F, G, C, A |
| [`DftPreRev`]  (Reverse Depth-First Traversal in Pre-Order)  | G, F, C, E, D, B, A |
| [`DftPostRev`] (Reverse Depth-First Traversal in Post-Order) | A, C, G, F, B, E, D |

*See each individual algorithm for code examples.*

[`Bft`]: https://docs.rs/traversal/*/traversal/struct.Bft.html
[`DftPre`]: https://docs.rs/traversal/*/traversal/struct.DftPre.html
[`DftPost`]: https://docs.rs/traversal/*/traversal/struct.DftPost.html
[`DftPreRev`]: https://docs.rs/traversal/*/traversal/struct.DftPreRev.html
[`DftPostRev`]: https://docs.rs/traversal/*/traversal/struct.DftPostRev.html

### All Paths and Longest Paths

[`DftPaths`] and [`DftLongestPaths`] are utilities for
iterating all paths and the longest paths in a tree.

*Given the same tree as the previous examples, then
[`DftPaths`] and [`DftLongestPaths`] produce the
following paths.*

[`DftPaths`]:
- A, B
- A, B, D
- A, B, E
- A, C
- A, C, F
- A, C, G

[`DftLongestPaths`]:
- A, B, D
- A, B, E
- A, C, F
- A, C, G

*See each individual algorithm for code examples.*

[`DftPaths`]: https://docs.rs/traversal/*/traversal/struct.DftPaths.html
[`DftLongestPaths`]: https://docs.rs/traversal/*/traversal/struct.DftLongestPaths.html

## Cycles

```text
  A <---+
 / \    |
B   D >-+
|   |   |
C   E >-+
```

[`DftCycles`]:
- A -> D (*implies D is connected with A*)
- A -> D -> E

*See each individual algorithm for code examples.*

[`DftCycles`]: https://docs.rs/traversal/*/traversal/struct.DftCycles.html
