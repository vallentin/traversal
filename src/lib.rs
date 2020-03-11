//! Traversal

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![warn(clippy::all)]

mod bft;
mod dft_longest_paths;
mod dft_paths;
mod dft_post;
mod dft_post_rev;
mod dft_pre;
mod dft_pre_rev;

pub use bft::*;
pub use dft_longest_paths::*;
pub use dft_paths::*;
pub use dft_post::*;
pub use dft_post_rev::*;
pub use dft_pre::*;
pub use dft_pre_rev::*;

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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn bft<'a, T, F, I>(root: &'a T, children: F) -> Bft<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    Bft::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_pre<'a, T, F, I>(root: &'a T, children: F) -> DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPre::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_post<'a, T, F, I>(root: &'a T, children: F) -> DftPost<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPost::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_pre_rev<'a, T, F, I>(root: &'a T, children: F) -> DftPreRev<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPreRev::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_post_rev<'a, T, F, I>(root: &'a T, children: F) -> DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPostRev::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_paths<'a, T, F, I>(root: &'a T, children: F) -> DftPaths<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftPaths::new(root, children)
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
/// // The `Fn(&Node) -> Iterator<Item = &Node>` returns
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
pub fn dft_longest_paths<'a, T, F, I>(root: &'a T, children: F) -> DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    DftLongestPaths::new(root, children)
}
