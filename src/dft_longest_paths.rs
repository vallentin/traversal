use std::iter::FusedIterator;
use std::mem;

use crate::DftPre;

/// Produces the longest paths using
/// Depth-First Traversal (in Pre-Order).
///
/// # Cycles
///
/// `DftLongestPaths` does not handle cycles. If any
/// cycles are present, then `DftLongestPaths` will
/// result in an infinite (never ending)
/// [`Iterator`].
///
/// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    path: Vec<&'a T>,
    iter: DftPre<'a, T, F, I>,
}

impl<'a, T, F, I> DftLongestPaths<'a, T, F, I>
where
    T: ?Sized,
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
    /// Create as `DftLongestPaths`.
    ///
    /// *[See `DftLongestPaths` for more information.][`DftLongestPaths`]*
    ///
    /// [`DftLongestPaths`]: struct.DftLongestPaths.html
    #[inline]
    pub fn new(root: &'a T, children: F) -> Self {
        let mut iter = DftPre::new(root, children);

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
    F: Fn(&'a T) -> I,
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
    F: Fn(&'a T) -> I,
    I: Iterator<Item = &'a T>,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Node(&'static str, &'static [Node]);

    #[test]
    fn dft_paths() {
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
