use std::iter::{Extend, FusedIterator};

/// Reverse [Depth-First Traversal] in Post-Order.
///
/// [Depth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
///
/// # Cycles
///
/// `DftPostRev` does not handle cycles. If any
/// cycles are present, then `DftPostRev` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
///
/// # Example
///
/// ```
/// use traversal::DftPostRev;
///
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
/// let iter = DftPostRev::new(&tree, |node| node.1.iter());
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
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    queue: Vec<(usize, &'a T)>,
    iter_children: F,
}

impl<'a, T, F, I> DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Creates a `DftPostRev`, where `root` is the
    /// starting `Node`.
    ///
    /// The `iter_children` [`FnMut`] is (lazily) called
    /// for each `Node` as needed, where the
    /// returned [`Iterator`] produces the child
    /// `Node`s for the given `Node`.
    ///
    /// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
    ///
    /// *[See `DftPostRev` for more information.][`DftPostRev`]*
    ///
    /// [`DftPostRev`]: struct.DftPostRev.html
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
    /// While `DftPostRev` does not require [`FusedIterator`],
    /// it assumes that no `Node`s are produced after
    /// a `None`.
    ///
    /// [`FusedIterator`]: https://doc.rust-lang.org/stable/std/iter/trait.FusedIterator.html
    #[inline]
    pub fn new(root: &'a T, iter_children: F) -> Self {
        Self {
            queue: vec![(0, root)],
            iter_children,
        }
    }
}

impl<'a, T, F, I> Iterator for DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((depth, node)) = self.queue.pop() {
            let children = (self.iter_children)(node);
            self.queue.extend(children.map(|child| (depth + 1, child)));

            Some((depth, node))
        } else {
            None
        }
    }
}

impl<'a, T, F, I> FusedIterator for DftPostRev<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use crate::DftPost;

    use super::*;

    #[derive(PartialEq, Debug)]
    struct Node(&'static str, &'static [Node]);

    #[rustfmt::skip]
    const TREE: Node = Node("A", &[
        Node("F", &[
            Node("I", &[]),
            Node("G", &[
                Node("H", &[])
            ])]),
        Node("B", &[
            Node("D", &[
                Node("E", &[])
            ]),
            Node("C", &[])]),
    ]);

    #[test]
    fn dft_post_rev() {
        let iter = DftPostRev::new(&TREE, |node| node.1.iter());
        let mut iter = iter.map(|(depth, node)| (depth, node.0));

        assert_eq!(iter.next(), Some((0, "A")));
        assert_eq!(iter.next(), Some((1, "B")));
        assert_eq!(iter.next(), Some((2, "C")));
        assert_eq!(iter.next(), Some((2, "D")));
        assert_eq!(iter.next(), Some((3, "E")));
        assert_eq!(iter.next(), Some((1, "F")));
        assert_eq!(iter.next(), Some((2, "G")));
        assert_eq!(iter.next(), Some((3, "H")));
        assert_eq!(iter.next(), Some((2, "I")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn dft_post() {
        let mut iter1 = DftPostRev::new(&TREE, |node| node.1.iter());

        let iter2 = DftPost::new(&TREE, |node| node.1.iter()).collect::<Vec<_>>();
        let mut iter2 = iter2.into_iter().rev();

        loop {
            let next1 = iter1.next();
            let next2 = iter2.next();

            if next1.is_none() && next2.is_none() {
                break;
            }

            assert_eq!(next1, next2);
        }
    }
}
