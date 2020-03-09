use std::iter::{Extend, FusedIterator};

/// Reverse Depth-First Traversal in Post-Order.
///
/// # Cycles
///
/// `DftPostRev` does not handle cycles. If any
/// cycles are present, then `DftPostRev` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftPostRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    queue: Vec<(usize, &'a T)>,
    children: F,
}

impl<'a, T, F, I> DftPostRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Create as `DftPostRev`.
    ///
    /// *[See `DftPostRev` for more information.][`DftPostRev`]*
    ///
    /// [`DftPostRev`]: struct.DftPostRev.html
    #[inline]
    pub fn new(root: &'a T, children: F) -> Self {
        Self {
            queue: vec![(0, root)],
            children,
        }
    }
}

impl<'a, T, F, I> Iterator for DftPostRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((depth, node)) = self.queue.pop() {
            let children = (self.children)(node);
            self.queue.extend(children.map(|child| (depth + 1, child)));

            Some((depth, node))
        } else {
            None
        }
    }
}

impl<'a, T, F, I> FusedIterator for DftPostRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(PartialEq, Debug)]
    struct Node(&'static str, &'static [Node]);

    #[test]
    fn dft_post_rev() {
        #[rustfmt::skip]
        let tree = Node("I", &[
            Node("D", &[
                Node("A", &[]),
                Node("C", &[
                    Node("B", &[])
                ])]),
            Node("H", &[
                Node("F", &[
                    Node("E", &[])
                ]),
                Node("G", &[])]),
        ]);

        let iter = DftPostRev::new(&tree, |node| node.1.iter());
        let mut iter = iter.map(|(depth, node)| (depth, node.0));

        assert_eq!(iter.next(), Some((0, "I")));
        assert_eq!(iter.next(), Some((1, "H")));
        assert_eq!(iter.next(), Some((2, "G")));
        assert_eq!(iter.next(), Some((2, "F")));
        assert_eq!(iter.next(), Some((3, "E")));
        assert_eq!(iter.next(), Some((1, "D")));
        assert_eq!(iter.next(), Some((2, "C")));
        assert_eq!(iter.next(), Some((3, "B")));
        assert_eq!(iter.next(), Some((2, "A")));
        assert_eq!(iter.next(), None);
    }
}
