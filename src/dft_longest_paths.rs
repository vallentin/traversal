use std::iter::FusedIterator;
use std::mem;

use crate::DftPre;

/// Produces the longest paths using
/// [Depth-First Traversal] (in Pre-Order).
///
/// [Depth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
///
/// # Cycles
///
/// `DftLongestPaths` does not handle cycles. If any
/// cycles are present, then `DftLongestPaths` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
///
/// # Example
///
/// ```
/// use traversal::DftLongestPaths;
///
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
/// let iter = DftLongestPaths::new(&tree, |node| node.1.iter());
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
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    path: Vec<&'a T>,
    iter: DftPre<'a, T, F, I>,
}

impl<'a, T, F, I> DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Creates a `DftLongestPaths`, where `root` is the
    /// starting `Node`.
    ///
    /// The `iter_children` [`FnMut`] is (lazily) called
    /// for each `Node` as needed, where the
    /// returned [`Iterator`] produces the child
    /// `Node`s for the given `Node`.
    ///
    /// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
    ///
    ///
    /// *[See `DftLongestPaths` for more information.][`DftLongestPaths`]*
    ///
    /// [`DftLongestPaths`]: struct.DftLongestPaths.html
    ///
    /// # "`FnOnce`"
    ///
    /// The [`FnMut`] is a [`FnOnce`] from the point-of-view of
    /// a `Node`, as `iter_children` is at most called once for
    /// each individual `Node`.
    ///
    /// [`FnMut`]: https://doc.rust-lang.org/std/ops/trait.FnMut.html
    /// [`FnOnce`]: https://doc.rust-lang.org/std/ops/trait.FnOnce.html
    ///
    /// # `FusedIterator`
    ///
    /// While `DftLongestPaths` does not require [`FusedIterator`],
    /// it assumes that no `Node`s are produced after
    /// a `None`.
    ///
    /// [`FusedIterator`]: https://doc.rust-lang.org/stable/std/iter/trait.FusedIterator.html
    #[inline]
    pub fn new(root: &'a T, iter_children: F) -> Self {
        let mut iter = DftPre::new(root, iter_children);

        // Safe to use `unwrap` as `DftPre` with `root` at least produces `root`
        Self {
            path: vec![iter.next().unwrap().1],
            iter,
        }
    }
}

impl<'a, T, F, I> Iterator for DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = Vec<&'a T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.path.is_empty() {
            None
        } else {
            while let Some((depth, node)) = self.iter.next() {
                if self.path.len() > depth {
                    let path = self.path.clone();

                    self.path.truncate(depth);
                    self.path.push(node);

                    return Some(path);
                } else {
                    self.path.push(node);
                }
            }

            Some(mem::replace(&mut self.path, Vec::new()))
        }
    }
}

impl<'a, T, F, I> FusedIterator for DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Node(&'static str, &'static [Node]);

    #[test]
    fn dft_longest_paths() {
        #[rustfmt::skip]
        let tree = Node("A", &[
            Node("B", &[
                Node("C", &[]),
                Node("D", &[
                    Node("E", &[])
                ])]),
            Node("F", &[
                Node("G", &[
                    Node("H", &[])
                ]),
                Node("I", &[])]),
        ]);

        let iter = DftLongestPaths::new(&tree, |node| node.1.iter());
        let mut iter = iter.map(|path| path.iter().map(|node| node.0).collect::<Vec<_>>());

        assert_eq!(iter.next(), Some(vec!["A", "B", "C"]));
        assert_eq!(iter.next(), Some(vec!["A", "B", "D", "E"]));
        assert_eq!(iter.next(), Some(vec!["A", "F", "G", "H"]));
        assert_eq!(iter.next(), Some(vec!["A", "F", "I"]));
        assert_eq!(iter.next(), None);
    }
}
