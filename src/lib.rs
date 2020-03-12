//! Traversal implements generic and lazy tree traversal algorithms.
//!
//! Includes:
//! - [Breadth-First Traversal] ([`Bft`])
//! - [Depth-First Traversal] in Pre-Order ([`DftPre`])
//! - [Depth-First Traversal] in Post-Order ([`DftPost`])
//! - Reverse [Depth-First Traversal] in Pre-Order ([`DftPreRev`])
//! - Reverse [Depth-First Traversal] in Post-Order ([`DftPostRev`])
//! <!---->
//! - All Paths ([`DftPaths`])
//! - Longest Paths ([`DftLongestPaths`])
//!
//! [Breadth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
//! [Depth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
//!
//! ## Generic
//!
//! Traversal uses [generics] (or [type parameters]) to be
//! flexible to use, and easy to implement and fit into existing
//! architecture.
//!
//! [generics]: https://doc.rust-lang.org/rust-by-example/generics.html
//! [type parameters]: https://doc.rust-lang.org/reference/types/parameters.html
//!
//! ## Laziness
//!
//! Laziness or [lazy evaluation] refers to evaluation being delayed
//! until needed.
//!
//! Traversal delays processing `Node`s and fetching child `Node`s
//! until [`Iterator::next`][`next`] is called.
//! When [`next`] is called, then traversal only processes the
//! `Node`s required for this iteration.
//!
//! [lazy evaluation]: https://en.wikipedia.org/wiki/Lazy_evaluation
//!
//! *From Rust's docs:*
//!
//! > *Iterators (and iterator [adapters]) are lazy. This means that just
//! > creating an iterator doesn't do a whole lot. Nothing really happens
//! > until you call [`next`].*
//! >
//! > &mdash; [`Iterator`] - [Laziness]
//!
//! [`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
//! [`next`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#tymethod.next
//!
//! [Laziness]: https://doc.rust-lang.org/std/iter/index.html#laziness
//! [adapters]: https://doc.rust-lang.org/std/iter/index.html#adapters
//!
//! # Algorithms
//!
//! ```test
//!      A
//!     / \
//!    B   C
//!   / \ / \
//!  D  E F  G
//! ```
//!
//! Given the above tree, then the following are the orders,
//! that each individual iterator / traversal algorithm produces.
//!
//! | Algorithm | Order |
//! |-----------|-------|
//! | [`Bft`]        (Breadth-First Traversal)                     | A, B, C, D, E, F, G |
//! | [`DftPre`]     (Depth-First Traversal in Pre-Order)          | A, B, D, E, C, F, G |
//! | [`DftPost`]    (Depth-First Traversal in Post-Order)         | D, E, B, F, G, C, A |
//! | [`DftPreRev`]  (Reverse Depth-First Traversal in Pre-Order)  | G, F, C, E, D, B, A |
//! | [`DftPostRev`] (Reverse Depth-First Traversal in Post-Order) | A, C, G, F, B, E, D |
//!
//! *See each individual algorithm for code examples.*
//!
//! [`Bft`]: struct.Bft.html
//! [`DftPre`]: struct.DftPre.html
//! [`DftPost`]: struct.DftPost.html
//! [`DftPreRev`]: struct.DftPreRev.html
//! [`DftPostRev`]: struct.DftPostRev.html
//!
//! ## All Paths and Longest Paths
//!
//! [`DftPaths`] and [`DftLongestPaths`] are utilities for
//! iterating all paths and the longest paths in a tree.
//!
//! *Given the same tree as the previous examples, then
//! [`DftPaths`] and [`DftLongestPaths`] produce the
//! following paths.*
//!
//! [`DftPaths`]:
//! - A, B
//! - A, B, D
//! - A, B, E
//! - A, C
//! - A, C, F
//! - A, C, G
//!
//! [`DftLongestPaths`]:
//! - A, B, D
//! - A, B, E
//! - A, C, F
//! - A, C, G
//!
//! *See each individual algorithm for code examples.*
//!
//! [`DftPaths`]: struct.DftPaths.html
//! [`DftLongestPaths`]: struct.DftLongestPaths.html

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![warn(clippy::all)]

mod bft;
mod dft_cycles;
mod dft_longest_paths;
mod dft_paths;
mod dft_post;
mod dft_post_rev;
mod dft_pre;
mod dft_pre_rev;

pub use bft::*;
pub use dft_cycles::*;
pub use dft_longest_paths::*;
pub use dft_paths::*;
pub use dft_post::*;
pub use dft_post_rev::*;
pub use dft_pre::*;
pub use dft_pre_rev::*;

use std::hash::Hash;

/// *[This is a shorthand for `Bft::new`, see `Bft` for more information.][`Bft`]*
///
/// [`Bft`]: struct.Bft.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("A", &[
///     Node("B", &[
///         Node("D", &[]),
///         Node("E", &[])
///     ]),
///     Node("C", &[
///         Node("F", &[]),
///         Node("G", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::bft(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = &Node>` into `Iterator<Item = &str>`
/// let mut iter = iter.map(|(depth, node)| (depth, node.0));
///
/// assert_eq!(iter.next(), Some((0, "A")));
/// assert_eq!(iter.next(), Some((1, "B")));
/// assert_eq!(iter.next(), Some((1, "C")));
/// assert_eq!(iter.next(), Some((2, "D")));
/// assert_eq!(iter.next(), Some((2, "E")));
/// assert_eq!(iter.next(), Some((2, "F")));
/// assert_eq!(iter.next(), Some((2, "G")));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn bft<'a, T, F, I>(root: &'a T, iter_children: F) -> Bft<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    Bft::new(root, iter_children)
}

/// *[This is a shorthand for `DftPre::new`, see `DftPre` for more information.][`DftPre`]*
///
/// [`DftPre`]: struct.DftPre.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("A", &[
///     Node("B", &[
///         Node("C", &[]),
///         Node("D", &[])
///     ]),
///     Node("E", &[
///         Node("F", &[]),
///         Node("G", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_pre(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = &Node>` into `Iterator<Item = &str>`
/// let mut iter = iter.map(|(depth, node)| (depth, node.0));
///
/// assert_eq!(iter.next(), Some((0, "A")));
/// assert_eq!(iter.next(), Some((1, "B")));
/// assert_eq!(iter.next(), Some((2, "C")));
/// assert_eq!(iter.next(), Some((2, "D")));
/// assert_eq!(iter.next(), Some((1, "E")));
/// assert_eq!(iter.next(), Some((2, "F")));
/// assert_eq!(iter.next(), Some((2, "G")));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_pre<'a, T, F, I>(root: &'a T, iter_children: F) -> DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPre::new(root, iter_children)
}

/// *[This is a shorthand for `DftPost::new`, see `DftPost` for more information.][`DftPost`]*
///
/// [`DftPost`]: struct.DftPost.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("G", &[
///     Node("C", &[
///         Node("A", &[]),
///         Node("B", &[])
///     ]),
///     Node("F", &[
///         Node("D", &[]),
///         Node("E", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_post(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = &Node>` into `Iterator<Item = &str>`
/// let mut iter = iter.map(|(depth, node)| (depth, node.0));
///
/// assert_eq!(iter.next(), Some((2, "A")));
/// assert_eq!(iter.next(), Some((2, "B")));
/// assert_eq!(iter.next(), Some((1, "C")));
/// assert_eq!(iter.next(), Some((2, "D")));
/// assert_eq!(iter.next(), Some((2, "E")));
/// assert_eq!(iter.next(), Some((1, "F")));
/// assert_eq!(iter.next(), Some((0, "G")));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_post<'a, T, F, I>(root: &'a T, iter_children: F) -> DftPost<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPost::new(root, iter_children)
}

/// *[This is a shorthand for `DftPreRev::new`, see `DftPreRev` for more information.][`DftPreRev`]*
///
/// [`DftPreRev`]: struct.DftPreRev.html
///
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("G", &[
///     Node("F", &[
///         Node("E", &[]),
///         Node("D", &[])
///     ]),
///     Node("C", &[
///         Node("B", &[]),
///         Node("A", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_pre_rev(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = &Node>` into `Iterator<Item = &str>`
/// let mut iter = iter.map(|(depth, node)| (depth, node.0));
///
/// assert_eq!(iter.next(), Some((2, "A")));
/// assert_eq!(iter.next(), Some((2, "B")));
/// assert_eq!(iter.next(), Some((1, "C")));
/// assert_eq!(iter.next(), Some((2, "D")));
/// assert_eq!(iter.next(), Some((2, "E")));
/// assert_eq!(iter.next(), Some((1, "F")));
/// assert_eq!(iter.next(), Some((0, "G")));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_pre_rev<'a, T, F, I>(root: &'a T, iter_children: F) -> DftPreRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPreRev::new(root, iter_children)
}

/// *[This is a shorthand for `DftPostRev::new`, see `DftPostRev` for more information.][`DftPostRev`]*
///
/// [`DftPostRev`]: struct.DftPostRev.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("A", &[
///     Node("E", &[
///         Node("G", &[]),
///         Node("F", &[])
///     ]),
///     Node("B", &[
///         Node("D", &[]),
///         Node("C", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_post_rev(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = &Node>` into `Iterator<Item = &str>`
/// let mut iter = iter.map(|(depth, node)| (depth, node.0));
///
/// assert_eq!(iter.next(), Some((0, "A")));
/// assert_eq!(iter.next(), Some((1, "B")));
/// assert_eq!(iter.next(), Some((2, "C")));
/// assert_eq!(iter.next(), Some((2, "D")));
/// assert_eq!(iter.next(), Some((1, "E")));
/// assert_eq!(iter.next(), Some((2, "F")));
/// assert_eq!(iter.next(), Some((2, "G")));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_post_rev<'a, T, F, I>(root: &'a T, iter_children: F) -> DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPostRev::new(root, iter_children)
}

/// *[This is a shorthand for `DftPaths::new`, see `DftPaths` for more information.][`DftPaths`]*
///
/// [`DftPaths`]: struct.DftPaths.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("A", &[
///     Node("B", &[
///         Node("C", &[]),
///         Node("D", &[])
///     ]),
///     Node("E", &[
///         Node("F", &[]),
///         Node("G", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_paths(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = Vec<&Node>>` into `Iterator<Item = Vec<&str>>`
/// let mut iter = iter.map(|path| path.iter().map(|node| node.0).collect::<Vec<_>>());
///
/// assert_eq!(iter.next(), Some(vec!["A", "B"]));
/// assert_eq!(iter.next(), Some(vec!["A", "B", "C"]));
/// assert_eq!(iter.next(), Some(vec!["A", "B", "D"]));
/// assert_eq!(iter.next(), Some(vec!["A", "E"]));
/// assert_eq!(iter.next(), Some(vec!["A", "E", "F"]));
/// assert_eq!(iter.next(), Some(vec!["A", "E", "G"]));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_paths<'a, T, F, I>(root: &'a T, iter_children: F) -> DftPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPaths::new(root, iter_children)
}

/// *[This is a shorthand for `DftLongestPaths::new`, see `DftLongestPaths` for more information.][`DftLongestPaths`]*
///
/// [`DftLongestPaths`]: struct.DftLongestPaths.html
///
/// # Example
///
/// ```
/// struct Node(&'static str, &'static [Node]);
///
/// let tree = Node("A", &[
///     Node("B", &[
///         Node("C", &[]),
///         Node("D", &[])
///     ]),
///     Node("E", &[
///         Node("F", &[]),
///         Node("G", &[])
///     ]),
/// ]);
///
/// // `&tree` represents the root `Node`.
/// // The `FnMut(&Node) -> Iterator<Item = &Node>` returns
/// // an `Iterator` to get the child `Node`s.
/// let iter = traversal::dft_longest_paths(&tree, |node| node.1.iter());
///
/// // Map `Iterator<Item = Vec<&Node>>` into `Iterator<Item = Vec<&str>>`
/// let mut iter = iter.map(|path| path.iter().map(|node| node.0).collect::<Vec<_>>());
///
/// assert_eq!(iter.next(), Some(vec!["A", "B", "C"]));
/// assert_eq!(iter.next(), Some(vec!["A", "B", "D"]));
/// assert_eq!(iter.next(), Some(vec!["A", "E", "F"]));
/// assert_eq!(iter.next(), Some(vec!["A", "E", "G"]));
/// assert_eq!(iter.next(), None);
/// ```
#[inline]
pub fn dft_longest_paths<'a, T, F, I>(root: &'a T, iter_children: F) -> DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftLongestPaths::new(root, iter_children)
}

/// *[This is a shorthand for `DftCycles::new`, see `DftCycles` for more information.][`DftCycles`]*
///
/// [`DftCycles`]: struct.DftCycles.html
///
/// # Example
///
/// ```
/// #[derive(PartialEq, Eq, Hash)]
/// struct Vertex(&'static str, Vec<usize>);
///
/// //   A <-+
/// //  /|\  |
/// // B | C |
/// //  \|/  |
/// //   D >-+
/// //
/// // Cycles:
/// // - A -> B -> D -> A
/// // - A -> D -> A
/// // - A -> C -> D -> A
/// let graph = vec![
///     Vertex("A", vec![1, 3, 2]), // 0
///     Vertex("B", vec![3]),       // 1
///     Vertex("C", vec![3]),       // 2
///     Vertex("D", vec![0]),       // 3
/// ];
///
/// let start = &graph[0]; // A
///
/// // `&tree` represents the root `Vertex`.
/// // The `FnMut(&Vertex) -> Iterator<Item = &Vertex>` returns
/// // an `Iterator` to get the connected vertices.
/// let mut cycles = traversal::dft_cycles(start, |vertex| {
///     vertex.1.iter().map(|&i| {
///         &graph[i]
///     })
/// });
///
/// // Map `Iterator<Item = Vec<&Vertex>>` into `Iterator<Item = Vec<&str>>`
/// let mut cycles = cycles.map(|path| path.iter().map(|vertex| vertex.0).collect::<Vec<_>>());
///
/// assert_eq!(cycles.next(), Some(vec!["A", "B", "D"]));
/// assert_eq!(cycles.next(), Some(vec!["A", "D"]));
/// assert_eq!(cycles.next(), Some(vec!["A", "C", "D"]));
/// assert_eq!(cycles.next(), None);
/// ```
#[inline]
pub fn dft_cycles<'a, T, F, I>(root: &'a T, iter_children: F) -> DftCycles<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
    T: Eq + Hash,
{
    DftCycles::new(root, iter_children)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Node(&'static str, &'static [Node]);

    #[rustfmt::skip]
    const TREE: Node = Node("A", &[
        Node("B", &[
            Node("D", &[]),
            Node("E", &[])
        ]),
        Node("C", &[
            Node("F", &[]),
            Node("G", &[])
        ]),
    ]);

    #[test]
    fn lib_example() {
        // If this example is changed, then update
        // both code and output in lib.rs and README.md.

        assert_eq!(
            bft(&TREE, |node| node.1.iter())
                .map(|(_, node)| node.0)
                .collect::<Vec<_>>(),
            vec!["A", "B", "C", "D", "E", "F", "G"],
        );

        assert_eq!(
            dft_pre(&TREE, |node| node.1.iter())
                .map(|(_, node)| node.0)
                .collect::<Vec<_>>(),
            vec!["A", "B", "D", "E", "C", "F", "G"],
        );

        assert_eq!(
            dft_post(&TREE, |node| node.1.iter())
                .map(|(_, node)| node.0)
                .collect::<Vec<_>>(),
            vec!["D", "E", "B", "F", "G", "C", "A"],
        );

        assert_eq!(
            dft_pre_rev(&TREE, |node| node.1.iter())
                .map(|(_, node)| node.0)
                .collect::<Vec<_>>(),
            vec!["G", "F", "C", "E", "D", "B", "A"],
        );

        assert_eq!(
            dft_post_rev(&TREE, |node| node.1.iter())
                .map(|(_, node)| node.0)
                .collect::<Vec<_>>(),
            vec!["A", "C", "G", "F", "B", "E", "D"],
        );
    }

    #[test]
    fn lib_example_paths() {
        // If this example is changed, then update
        // both code and output in lib.rs and README.md.

        assert_eq!(
            DftPaths::new(&TREE, |node| node.1.iter())
                .map(|path| path.iter().map(|node| node.0).collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![
                vec!["A", "B"],
                vec!["A", "B", "D"],
                vec!["A", "B", "E"],
                vec!["A", "C"],
                vec!["A", "C", "F"],
                vec!["A", "C", "G"],
            ],
        );

        assert_eq!(
            DftLongestPaths::new(&TREE, |node| node.1.iter())
                .map(|path| path.iter().map(|node| node.0).collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            vec![
                vec!["A", "B", "D"],
                vec!["A", "B", "E"],
                vec!["A", "C", "F"],
                vec!["A", "C", "G"],
            ],
        );
    }
}
