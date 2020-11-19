#![no_std]
#![deny(missing_debug_implementations, missing_copy_implementations)]
#![doc(html_root_url = "https://docs.rs/log/2.0.0")]

//! This crate provides set operations on sorted, deduplicated iterators. Unless otherwise
//! specified, all iterator parameters in this crate should yield elements in ascending order with
//! consecutive repeated elements removed. If this is upheld, then all iterators returned by this
//! crate will share those properties.

#[cfg(test)]
extern crate std;

#[cfg(test)]
mod tests;

use core::cmp::{self, Ordering};
use core::fmt::{self, Debug};

/// Compare two sets represented by sorted, deduplicated iterators.
///
/// The return value represents a partial ordering based on set inclusion. If the iterators 
/// are equal, then `Some(Equal)` is returned. If `a` is a subset of `b` then `Some(Less)` 
/// is returned. If `a` is a superset of `b` then `Some(Greater)` is returned. Otherwise, 
/// `None` is returned. If `a` and `b` are not sorted or contain duplicate values, the return 
/// value is unspecified.
///
/// Time complexity: `O(a.len() + b.len())`.
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering::{Equal, Greater, Less};
/// use iter_set::cmp;
///
/// let a = [1, 2, 3];
/// let b = [2, 3];
/// let c = [2, 3, 4];
///
/// assert_eq!(cmp(&a, &b), Some(Greater));
/// assert_eq!(cmp(&b, &b), Some(Equal));
/// assert_eq!(cmp(&b, &c), Some(Less));
/// assert_eq!(cmp(&a, &c), None);
/// ```
pub fn cmp<T, L, R>(a: L, b: R) -> Option<Ordering>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).try_fold(Ordering::Equal, cmp_fold)
}

/// Compare two sets represented by sorted, deduplicated iterators, using a key extraction function.
///
/// See [`cmp()`].
///
/// # Examples
///
/// ```
/// use std::cmp::Ordering::{Equal, Greater, Less};
/// use iter_set::cmp_by_key;
///
/// let a = [(1, "a"), (2, "b"), (3, "c")];
/// let b = [(2, "d"), (3, "a")];
/// let c = [(2, "b"), (3, "c"), (4, "d")];
///
/// assert_eq!(cmp_by_key(&a, &b, |&(key, _)| key), Some(Greater));
/// assert_eq!(cmp_by_key(&b, &b, |&(key, _)| key), Some(Equal));
/// assert_eq!(cmp_by_key(&b, &c, |&(key, _)| key), Some(Less));
/// assert_eq!(cmp_by_key(&a, &c, |&(key, _)| key), None);
/// ```
pub fn cmp_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> Option<Ordering>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).try_fold(Ordering::Equal, cmp_fold)
}

/// Compare two sets represented by sorted, deduplicated iterators, using a comparator function.
///
/// See [`cmp()`].
///
/// # Examples
///
/// Using a custom comparator to reverse the ordering
///
/// ```
/// use std::cmp::Ordering::{Equal, Greater, Less};
/// use iter_set::cmp_by;
///
/// let a = [3, 2, 1];
/// let b = [3, 2];
/// let c = [4, 3, 2];
///
/// assert_eq!(cmp_by(&a, &b, |l, r| Ord::cmp(r, l)), Some(Greater));
/// assert_eq!(cmp_by(&b, &b, |l, r| Ord::cmp(r, l)), Some(Equal));
/// assert_eq!(cmp_by(&b, &c, |l, r| Ord::cmp(r, l)), Some(Less));
/// assert_eq!(cmp_by(&a, &c, |l, r| Ord::cmp(r, l)), None);
/// ```
pub fn cmp_by<T, L, R, F>(a: L, b: R, cmp: F) -> Option<Ordering>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).try_fold(Ordering::Equal, cmp_fold)
}

fn cmp_fold<T>(init: Ordering, next: Inclusion<T>) -> Option<Ordering> {
    use Ordering::*;

    match (init, next.ordering()) {
        (Less, Greater) | (Greater, Less) => None,
        (Equal, x) | (x, Equal) => Some(x),
        (Greater, Greater) => Some(Greater),
        (Less, Less) => Some(Less),
    }
}

/// Take the union of two sets represented by sorted, deduplicated iterators.
///
/// If an element is in both iterators, then only the one from `a` is yielded.
/// This behaviour can be overridden by using [`union_by()`].
///
/// Time complexity: `O(a.len() + b.len())`.
///
/// # Examples
///
/// ```
/// use iter_set::union;
///
/// let a = [1, 2];
/// let b = [2, 3];
///
/// assert!(union(&a, &b).eq(&[1, 2, 3]));
/// ```
pub fn union<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).map(Inclusion::union)
}

/// Take the union of two sets represented by sorted, deduplicated iterators, using a comparator
/// function.
///
/// Note that since this passes elements to the comparator function as `&mut T`, you can swap them
/// to override the default behaviour of returning duplicate elements from `a`.
///
/// See [`union()`].
///
/// # Examples
///
/// Using the comparator function to perform a 'deep union'
///
/// ```
/// use std::cmp::Ordering::{self, Equal, Greater, Less};
/// use iter_set::union_by;
///
/// #[derive(Debug, Eq, PartialEq)]
/// enum Foo {
///     Zero,
///     Some(Vec<u32>),
/// }
///
/// fn combine(l: &mut Foo, r: &mut Foo) -> Ordering {
///     match (l, r) {
///         (Foo::Zero, Foo::Zero) => Equal,
///         (Foo::Zero, Foo::Some(_)) => Less,
///         (Foo::Some(_), Foo::Zero) => Greater,
///         (Foo::Some(l), Foo::Some(r)) => {
///             l.append(r);
///             Equal
///         }
///     }
/// }
///
/// let lhs = vec![Foo::Zero, Foo::Some(vec![1, 2])];
/// let rhs = vec![Foo::Some(vec![3])];
///
/// let union: Vec<_> = union_by(lhs, rhs, combine).collect();
/// assert_eq!(union, vec![Foo::Zero, Foo::Some(vec![1, 2, 3])]);
/// ```
pub fn union_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).map(Inclusion::union)
}

/// Take the union of two sets represented by sorted, deduplicated iterators, using a key extraction
/// function.
///
/// See [`union()`].
///
/// # Examples
///
/// ```
/// use iter_set::union_by_key;
///
/// let a = [(1, "a"), (2, "a")];
/// let b = [(2, "b"), (3, "b")];
///
/// assert!(union_by_key(&a, &b, |&(key, _)| key).eq(&[(1, "a"), (2, "a"), (3, "b")]));
/// ```
pub fn union_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).map(Inclusion::union)
}

/// Take the intersection of two sets represented by sorted, deduplicated iterators.
///
/// The elements returned will all be from `a`. This behaviour can be overridden by
/// using [`intersection_by()`].
///
/// Time complexity: `O(a.len() + b.len())`.
///
/// # Examples
///
/// ```
/// use iter_set::intersection;
///
/// let a = [1, 2];
/// let b = [2, 3];
///
/// assert!(intersection(&a, &b).eq(&[2]));
/// ```
pub fn intersection<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(Inclusion::intersection)
}

/// Take the intersection of two sets represented by sorted, deduplicated iterators, using a 
/// comparator function.
///
/// Note that since this passes elements to the comparator function as `&mut T`, you can swap them
/// to override the default behaviour of returning duplicate elements from `a`.
///
/// See [`intersection()`].
///
/// # Examples
///
/// Using the comparator function to choose which iterator to take from.
///
/// ```
/// use std::cmp::Ordering::{self, Equal};
/// use std::mem::swap;
/// use iter_set::intersection_by;
///
/// let mut a = [(1, vec![2]), (2, vec![])];
/// let mut b = [(2, vec![1]), (3, vec![])];
///
/// fn compare(l: &mut (u32, Vec<i32>), r: &mut (u32, Vec<i32>)) -> Ordering {
///     match Ord::cmp(&l.0, &r.0) {
///        Equal => {
///            if r.1.len() > l.1.len() {
///                swap(r, l);
///            }
///            Equal
///        }
///        neq => neq,
///     }
/// }
///
/// assert!(intersection_by(&mut a, &mut b, |l, r| compare(*l, *r)).eq(&[(2, vec![1])]));
/// ```
pub fn intersection_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(Inclusion::intersection)
}

/// Take the intersection of two sets represented by sorted, deduplicated iterators, using a key
/// extraction function.
///
/// See [`intersection()`].
///
/// # Examples
///
/// ```
/// use iter_set::intersection_by_key;
///
/// let a = [(1, "a"), (2, "a")];
/// let b = [(2, "b"), (3, "b")];
///
/// assert!(intersection_by_key(&a, &b, |&(key, _)| key).eq(&[(2, "a")]));
/// ```
pub fn intersection_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(Inclusion::intersection)
}

/// Take the difference of two sets (elements in `a` but not in `b`) represented by sorted,
/// deduplicated iterators.
///
/// Time complexity: `O(a.len() + b.len())`.
///
/// # Examples
///
/// ```
/// use iter_set::difference;
///
/// let a = [1, 2];
/// let b = [2, 3];
///
/// assert!(difference(&a, &b).eq(&[1]));
/// ```
pub fn difference<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(Inclusion::difference)
}

/// Take the difference of two sets represented by sorted, deduplicated iterators, using 
/// a comparator function.
///
/// See [`difference()`].
pub fn difference_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(Inclusion::difference)
}

/// Take the difference of two sets represented by sorted, deduplicated iterators, using a key
/// extraction function.
///
/// See [`difference()`].
pub fn difference_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(Inclusion::difference)
}

/// Take the symmetric_difference of two sets represented by sorted, deduplicated iterators.
///
/// Time complexity: `O(a.len() + b.len())`.
///
/// # Examples
///
/// ```
/// use iter_set::symmetric_difference;
///
/// let a = [1, 2];
/// let b = [2, 3];
///
/// assert!(symmetric_difference(&a, &b).eq(&[1, 3]));
/// ```
pub fn symmetric_difference<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(Inclusion::symmetric_difference)
}

/// Take the symmetric_difference of two sets represented by sorted, deduplicated iterators, 
/// using a comparator function.
///
/// See [`symmetric_difference()`].
pub fn symmetric_difference_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(Inclusion::symmetric_difference)
}

/// Take the symmetric_difference of two sets represented by sorted, deduplicated iterators, using a
/// key extraction function.
///
/// See [`symmetric_difference()`].
pub fn symmetric_difference_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(Inclusion::symmetric_difference)
}

/// Interleave two sorted, deduplicated iterators in sorted order and classify each element according
/// to its source.
///
/// # Examples
///
/// ```
/// use iter_set::{classify, Inclusion};
///
/// let a = [1, 2];
/// let b = [2, 3];
///
/// assert!(classify(&a, &b).eq(vec![Inclusion::Left(&1), Inclusion::Both(&2, &2), Inclusion::Right(&3)]));
/// ```
pub fn classify<T, L, R>(a: L, b: R) -> Classify<L::IntoIter, R::IntoIter>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    Classify::new(a, b)
}

/// Interleave two sorted, deduplicated iterators in sorted order and classify each element according
/// to its source, using a comparator function.
///
/// See [`classify()`].
pub fn classify_by<T, L, R, F>(a: L, b: R, cmp: F) -> ClassifyBy<L::IntoIter, R::IntoIter, F>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    ClassifyBy {
        inner: Classify::new(a, b),
        cmp,
    }
}

/// Interleave two sorted, deduplicated iterators in sorted order and classify each element according
/// to its source, using a key extraction function.
///
/// See [`classify()`].
pub fn classify_by_key<T, L, R, K, F>(
    a: L,
    b: R,
    key: F,
) -> ClassifyByKey<L::IntoIter, R::IntoIter, F>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    ClassifyByKey {
        inner: Classify::new(a, b),
        key,
    }
}

/// An iterator that interleaves two sorted, deduplicated iterators in sorted order and classifies
/// each element according to its source.
///
/// This `struct` is created by the [`classify()`] function. See its documentation
/// for more.
pub struct Classify<L, R>
where
    L: Iterator,
    R: Iterator,
{
    lhs: PutBack<L>,
    rhs: PutBack<R>,
}

impl<T, L, R> Classify<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    fn new(
        lhs: impl IntoIterator<IntoIter = L, Item = T>,
        rhs: impl IntoIterator<IntoIter = R, Item = T>,
    ) -> Self {
        Classify {
            lhs: PutBack::new(lhs.into_iter()),
            rhs: PutBack::new(rhs.into_iter()),
        }
    }

    fn next_by<F>(&mut self, mut cmp: F) -> Option<Inclusion<T>>
    where
        F: FnMut(&mut T, &mut T) -> Ordering,
    {
        match (self.lhs.next(), self.rhs.next()) {
            (Some(mut l), Some(mut r)) => match cmp(&mut l, &mut r) {
                Ordering::Less => {
                    self.rhs.put_back(r);
                    Some(Inclusion::Left(l))
                }
                Ordering::Equal => Some(Inclusion::Both(l, r)),
                Ordering::Greater => {
                    self.lhs.put_back(l);
                    Some(Inclusion::Right(r))
                }
            },
            (Some(l), None) => Some(Inclusion::Left(l)),
            (None, Some(r)) => Some(Inclusion::Right(r)),
            (None, None) => return None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lmin, lmax) = self.lhs.iter.size_hint();
        let (rmin, rmax) = self.rhs.iter.size_hint();
        let min = cmp::max(lmin, rmin);
        let max = match (lmax, rmax) {
            (Some(lmax), Some(rmax)) => lmax.checked_add(rmax),
            _ => None,
        };
        (min, max)
    }
}

/// The sets an element is included in.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Inclusion<T> {
    // The element is in the left set only.
    Left(T),
    // The element is in both sets.
    Both(T, T),
    // The element is in the right set only.
    Right(T),
}

impl<T> Inclusion<T> {
    /// Return the element, whichever set it is in. If it is in both sets, the left element is returned.
    pub fn union(self) -> T {
        match self {
            Inclusion::Left(l) => l,
            Inclusion::Both(l, _) => l,
            Inclusion::Right(r) => r,
        }
    }

    /// Return the element if it is in both sets. The left element is returned.
    pub fn intersection(self) -> Option<T> {
        match self {
            Inclusion::Left(_) | Inclusion::Right(_) => None,
            Inclusion::Both(l, _) => Some(l),
        }
    }

    /// Return the element if it is in the left set.
    pub fn difference(self) -> Option<T> {
        match self {
            Inclusion::Left(l) => Some(l),
            Inclusion::Both(_, _) | Inclusion::Right(_) => None,
        }
    }

    /// Return the element if it is in exactly one set.
    pub fn symmetric_difference(self) -> Option<T> {
        match self {
            Inclusion::Left(l) => Some(l),
            Inclusion::Both(_, _) => None,
            Inclusion::Right(r) => Some(r),
        }
    }

    /// Return an [`Ordering`] based on where the element is from.
    /// * `Ordering::Less`: from the right set.
    /// * `Ordering::Equal`: from both sets
    /// * `Ordering::Greater`: from the left set.
    pub fn ordering(&self) -> Ordering {
        match self {
            Inclusion::Left(_) => Ordering::Greater,
            Inclusion::Both(_, _) => Ordering::Equal,
            Inclusion::Right(_) => Ordering::Less,
        }
    }
}

impl<T, L, R> Iterator for Classify<L, R>
where
    T: Ord,
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = Inclusion<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_by(|l, r| Ord::cmp(l, r))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.size_hint()
    }
}

/// An iterator that interleaves two sorted, deduplicated iterators in sorted order and classifies
/// each element according to its source, using a comparator function.
///
/// This `struct` is created by the [`classify_by()`] function. See its
/// documentation for more.
pub struct ClassifyBy<L, R, F>
where
    L: Iterator,
    R: Iterator,
{
    inner: Classify<L, R>,
    cmp: F,
}

impl<T, L, R, F> Iterator for ClassifyBy<L, R, F>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    type Item = Inclusion<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_by(&mut self.cmp)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator that interleaves two sorted, deduplicated iterators in sorted order and classifies
/// each element according to its source, using a key extraction function.
///
/// This `struct` is created by the [`classify_by_key()`] function. See its
/// documentation for more.
pub struct ClassifyByKey<L, R, F>
where
    L: Iterator,
    R: Iterator,
{
    inner: Classify<L, R>,
    key: F,
}

impl<T, L, R, K, F> Iterator for ClassifyByKey<L, R, F>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    type Item = Inclusion<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let key = &mut self.key;
        self.inner.next_by(|l, r| Ord::cmp(&key(l), &key(r)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

struct PutBack<I: Iterator> {
    iter: I,
    next: Option<I::Item>,
}

impl<I: Iterator> PutBack<I> {
    fn new(iter: I) -> Self {
        PutBack { iter, next: None }
    }

    fn put_back(&mut self, item: I::Item) {
        debug_assert!(self.next.is_none());
        self.next = Some(item);
    }
}

impl<I: Iterator> Iterator for PutBack<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.is_some() {
            self.next.take()
        } else {
            self.iter.next()
        }
    }
}

impl<L, R> Debug for Classify<L, R>
where
    L: Debug + Iterator,
    R: Debug + Iterator,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Classify")
            .field("lhs", &self.lhs.iter)
            .field("rhs", &self.rhs.iter)
            .finish()
    }
}

impl<L, R, F> Debug for ClassifyBy<L, R, F>
where
    L: Debug + Iterator,
    R: Debug + Iterator,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ClassifyBy")
            .field("lhs", &self.inner.lhs.iter)
            .field("rhs", &self.inner.rhs.iter)
            .finish()
    }
}

impl<L, R, F> Debug for ClassifyByKey<L, R, F>
where
    L: Debug + Iterator,
    R: Debug + Iterator,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ClassifyByKey")
            .field("lhs", &self.inner.lhs.iter)
            .field("rhs", &self.inner.rhs.iter)
            .finish()
    }
}
