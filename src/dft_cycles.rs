use std::collections::HashSet;
use std::hash::Hash;
use std::iter::FusedIterator;

/// Produces all [cycle] paths using
/// [Depth-First Traversal] (in Pre-Order).
///
/// [Depth-First Traversal]: https://en.wikipedia.org/wiki/Tree_traversal
///
/// `DftCycles` produces all paths that contain a [cycle].
/// Thereby all [`Vec`]`<T>`s produced are a path
/// containing a cycle, as in `last()` is connected
/// to `first()`.
///
/// [`Vec`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html
/// [`last()`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.last
/// [`first()`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.first
///
/// [cycle]: https://en.wikipedia.org/wiki/Cycle_(graph_theory)
///
/// # Example
///
/// ```
/// use traversal::DftCycles;
///
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
/// let mut cycles = DftCycles::new(start, |vertex| {
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
#[allow(missing_debug_implementations)]
#[derive(Clone)]
pub struct DftCycles<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
    T: Eq + Hash,
{
    queue: Vec<(usize, &'a T)>,
    path: Vec<&'a T>,
    visited: HashSet<&'a T>,
    iter_connections: F,
}

impl<'a, T, F, I> DftCycles<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
    T: Eq + Hash,
{
    /// Creates a `DftCycles`, where `root` is the
    /// starting `Node`.
    ///
    /// The `iter_connections` [`FnMut`] is (lazily) called
    /// for each `Node` as needed, where the
    /// returned [`Iterator`] produces the child
    /// `Node`s for the given `Node`.
    ///
    /// [`Iterator`]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
    ///
    /// *[See `DftCycles` for more information.][`DftCycles`]*
    ///
    /// [`DftCycles`]: struct.DftCycles.html
    ///
    /// # "`FnOnce`"
    ///
    /// The [`FnMut`] is a [`FnOnce`] from the point-of-view of
    /// a `Node`, as `iter_connections` is at most called once for
    /// each individual `Node`.
    ///
    /// [`FnMut`]: https://doc.rust-lang.org/std/ops/trait.FnMut.html
    /// [`FnOnce`]: https://doc.rust-lang.org/std/ops/trait.FnOnce.html
    ///
    /// # `FusedIterator`
    ///
    /// While `DftCycles` does not require [`FusedIterator`],
    /// it assumes that no `Node`s are produced after
    /// a `None`.
    ///
    /// [`FusedIterator`]: https://doc.rust-lang.org/stable/std/iter/trait.FusedIterator.html
    #[inline]
    pub fn new(root: &'a T, iter_connections: F) -> Self {
        Self {
            queue: vec![(0, root)],
            path: Vec::new(),
            visited: HashSet::new(),
            iter_connections,
        }
    }
}

impl<'a, T, F, I> Iterator for DftCycles<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
    T: Eq + Hash,
{
    type Item = Vec<&'a T>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((depth, node)) = self.queue.pop() {
            if depth < self.path.len() {
                let (path, visited) = (&mut self.path, &mut self.visited);

                path.drain(depth..).for_each(|node| {
                    visited.remove(node);
                });
            }

            if !self.visited.insert(node) {
                return Some(self.path.clone());
            }

            self.path.push(node);

            let children = (self.iter_connections)(node);

            let children = children.collect::<Vec<_>>();
            let children = children.into_iter().rev();

            self.queue.extend(children.map(|child| (depth + 1, child)));
        }

        None
    }
}

impl<'a, T, F, I> FusedIterator for DftCycles<'a, T, F, I>
where
    T: ?Sized,
    F: FnMut(&'a T) -> I,
    I: Iterator<Item = &'a T>,
    T: Eq + Hash,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(PartialEq, Eq, Hash)]
    struct Vertex(&'static str, Vec<usize>);

    #[test]
    fn dft_cycles() {
        //   A <----+
        //  /  \    |
        // B >- D >-+
        //  \  /    |
        //   C >----+
        //
        // Cycles:
        // - A -> B -> C -> A
        // - A -> B -> C -> D -> A
        // - A -> B -> D -> A
        // - A -> D -> A
        let graph = vec![
            Vertex("A", vec![1, 3]), // 0
            Vertex("B", vec![2, 3]), // 1
            Vertex("C", vec![0, 3]), // 2
            Vertex("D", vec![0]),    // 3
        ];

        let start = &graph[0]; // A

        let cycles = DftCycles::new(start, |vertex| vertex.1.iter().map(|&i| &graph[i]));
        let mut cycles = cycles.map(|path| path.iter().map(|vertex| vertex.0).collect::<Vec<_>>());

        assert_eq!(cycles.next(), Some(vec!["A", "B", "C"]));
        assert_eq!(cycles.next(), Some(vec!["A", "B", "C", "D"]));
        assert_eq!(cycles.next(), Some(vec!["A", "B", "D"]));
        assert_eq!(cycles.next(), Some(vec!["A", "D"]));
        assert_eq!(cycles.next(), None);
    }
}
