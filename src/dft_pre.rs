use std::iter::{Extend, FusedIterator};

/// Depth-First Traversal in Pre-Order.
///
/// # Cycles
///
/// `DftPre` does not handle cycles. If any
/// cycles are present, then `DftPre` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    queue: Vec<(usize, &'a T)>,
    children: F,
}

impl<'a, T, F, I> DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Create as `DftPre`.
    ///
    /// *[See `DftPre` for more information.][`DftPre`]*
    ///
    /// [`DftPre`]: struct.DftPre.html
    #[inline]
    pub fn new(root: &'a T, children: F) -> Self {
        Self {
            queue: vec![(0, root)],
            children,
        }
    }
}

impl<'a, T, F, I> Iterator for DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = (usize, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((depth, node)) = self.queue.pop() {
            let children = (self.children)(node);

            let children = children.collect::<Vec<_>>();
            let children = children.into_iter().rev();

            self.queue.extend(children.map(|child| (depth + 1, child)));

            Some((depth, node))
        } else {
            None
        }
    }
}

impl<'a, T, F, I> FusedIterator for DftPre<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use std::slice::Iter;

    use super::*;

    struct Node(&'static str, &'static [Node]);

    trait NodeNoSize<'a, T: 'a> {
        type Iter: Iterator<Item = &'a T>;

        fn title(&self) -> &'static str;
        fn iter_children(&self) -> Self::Iter;
    }

    impl<'a> NodeNoSize<'a, Node> for Node {
        type Iter = Iter<'a, Self>;

        #[inline]
        fn title(&self) -> &'static str {
            self.0
        }

        #[inline]
        fn iter_children(&self) -> Self::Iter {
            self.1.iter()
        }
    }

    #[rustfmt::skip]
    const TREE: Node = Node("A", &[
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

    #[test]
    fn dft_pre() {
        let iter = DftPre::new(&TREE, |node| node.1.iter());
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
    fn dft_pre_no_size() {
        let root: &dyn NodeNoSize<Node, Iter = Iter<Node>> = &TREE;

        let iter = DftPre::new(root, |node| {
            node.iter_children()
                .map(|node| node as &dyn NodeNoSize<Node, Iter = Iter<Node>>)
        });
        let mut iter = iter.map(|(depth, node)| (depth, node.title()));

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
}
