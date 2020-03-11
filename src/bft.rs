use std::collections::VecDeque;
use std::iter::{Extend, FusedIterator};

/// [Breadth-First Traversal] (or Level Order Traversal).
///
/// [Breadth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
///
/// # Cycles
///
/// `Bft` does not handle cycles. If any
/// cycles are present, then `Bft` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
///
/// # Example
///
/// ```
/// use traversal::Bft;
///
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
/// let iter = Bft::new(&tree, |node| node.1.iter());
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
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct Bft<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    queue: VecDeque<(usize, &'a T)>,
    children: F,
}

impl<'a, T, F, I> Bft<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Creates a `Bft`, where `root` is the
    /// starting `Node`.
    ///
    /// The `children` [`Fn`] is (lazily) called
    /// for each `Node` as needed, where the
    /// returned [`Iterator`] produces the child
    /// `Node`s for the given `Node`.
    ///
    /// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
    ///
    /// *[See `Bft` for more information.][`Bft`]*
    ///
    /// [`Bft`]: struct.Bft.html
    ///
    /// # "`FnOnce`"
    ///
    /// The [`Fn`] is a [`FnOnce`] from the point-of-view of
    /// a `Node`, as `children` is at most called once for
    /// each individual `Node`.
    ///
    /// [`Fn`]: https://doc.rust-lang.org/std/ops/trait.Fn.html
    /// [`FnOnce`]: https://doc.rust-lang.org/std/ops/trait.FnOnce.html
    ///
    /// # `FusedIterator`
    ///
    /// While `Bft` does not require [`FusedIterator`],
    /// it assumes that no `Node`s are produced after
    /// a `None`.
    ///
    /// [`FusedIterator`]: https://doc.rust-lang.org/stable/std/iter/trait.FusedIterator.html
    #[inline]
    pub fn new(root: &'a T, children: F) -> Self {
        Self {
            queue: VecDeque::from(vec![(0, root)]),
            children,
        }
    }
}

impl<'a, T, F, I> Iterator for Bft<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = (usize, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((depth, node)) = self.queue.pop_front() {
            let children = (self.children)(node);
            self.queue.extend(children.map(|child| (depth + 1, child)));

            Some((depth, node))
        } else {
            None
        }
    }
}

impl<'a, T, F, I> FusedIterator for Bft<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Node(&'static str, &'static [Node]);

    #[test]
    fn bft() {
        #[rustfmt::skip]
        let tree = Node("A", &[
            Node("B", &[
                Node("D", &[]),
                Node("E", &[
                    Node("H", &[])
                ])]),
            Node("C", &[
                Node("F", &[
                    Node("I", &[])
                ]),
                Node("G", &[])]),
        ]);

        let iter = Bft::new(&tree, |node| node.1.iter());
        let mut iter = iter.map(|(depth, node)| (depth, node.0));

        assert_eq!(iter.next(), Some((0, "A")));
        assert_eq!(iter.next(), Some((1, "B")));
        assert_eq!(iter.next(), Some((1, "C")));
        assert_eq!(iter.next(), Some((2, "D")));
        assert_eq!(iter.next(), Some((2, "E")));
        assert_eq!(iter.next(), Some((2, "F")));
        assert_eq!(iter.next(), Some((2, "G")));
        assert_eq!(iter.next(), Some((3, "H")));
        assert_eq!(iter.next(), Some((3, "I")));
        assert_eq!(iter.next(), None);
    }
}
