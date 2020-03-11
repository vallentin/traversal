use std::collections::VecDeque;
use std::iter::FusedIterator;

/// Reverse Depth-First Traversal in Pre-Order.
///
/// # Cycles
///
/// `DftPreRev` does not handle cycles. If any
/// cycles are present, then `DftPreRev` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
///
/// # Example
///
/// ```
/// use traversal::DftPreRev;
///
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
/// let iter = DftPreRev::new(&tree, |node| node.1.iter());
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
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftPreRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// `children(self.queue[i])` has been called for all `i < visited`
    visited: usize,
    current_depth: usize,
    queue: VecDeque<(usize, &'a T)>,
    children: F,
}

impl<'a, T, F, I> DftPreRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Create as `DftPreRev`.
    ///
    /// *[See `DftPreRev` for more information.][`DftPreRev`]*
    ///
    /// [`DftPreRev`]: struct.DftPreRev.html
    #[inline]
    pub fn new(root: &'a T, children: F) -> Self {
        Self {
            visited: 0,
            current_depth: 0,
            queue: VecDeque::from(vec![(0, root)]),
            children,
        }
    }
}

impl<'a, T, F, I> Iterator for DftPreRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    type Item = (usize, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.queue.is_empty() {
            None
        } else {
            // Exhaust all children for the first branch
            loop {
                let i = self.visited;
                let (depth, node) = if let Some(&node) = self.queue.get(i) {
                    node
                } else {
                    break;
                };

                // This node is not a child nor a sibling
                if self.current_depth > depth {
                    break;
                }

                let before_len = self.queue.len();

                for child in (self.children)(node) {
                    self.queue.insert(i + 1, (depth + 1, child));
                }
                self.visited += 1;

                self.current_depth = depth;

                // The previous node produced no children
                if self.queue.len() == before_len {
                    break;
                }
            }

            let node = self.queue.remove(self.visited - 1).unwrap();
            self.visited -= 1;

            self.current_depth = node.0;

            Some(node)
        }
    }
}

impl<'a, T, F, I> FusedIterator for DftPreRev<'a, T, F, I>
where
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use crate::DftPre;

    use super::*;

    #[derive(PartialEq, Debug)]
    struct Node(&'static str, &'static [Node]);

    #[rustfmt::skip]
    const TREE: Node = Node("I", &[
        Node("H", &[
            Node("G", &[]),
            Node("F", &[
                Node("E", &[])
            ])]),
        Node("D", &[
            Node("C", &[
                Node("B", &[])
            ]),
            Node("A", &[])]),
    ]);

    #[test]
    fn dft_pre_rev() {
        let iter = DftPreRev::new(&TREE, |node| node.1.iter());
        let mut iter = iter.map(|(depth, node)| (depth, node.0));

        assert_eq!(iter.next(), Some((2, "A")));
        assert_eq!(iter.next(), Some((3, "B")));
        assert_eq!(iter.next(), Some((2, "C")));
        assert_eq!(iter.next(), Some((1, "D")));
        assert_eq!(iter.next(), Some((3, "E")));
        assert_eq!(iter.next(), Some((2, "F")));
        assert_eq!(iter.next(), Some((2, "G")));
        assert_eq!(iter.next(), Some((1, "H")));
        assert_eq!(iter.next(), Some((0, "I")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn dft_pre() {
        let mut iter1 = DftPreRev::new(&TREE, |node| node.1.iter());

        let iter2 = DftPre::new(&TREE, |node| node.1.iter()).collect::<Vec<_>>();
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
