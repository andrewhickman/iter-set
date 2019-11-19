#![deny(missing_debug_implementations, missing_copy_implementations)]

//! This crate provides set operations on sorted, deduplicated iterators. Unless otherwise
//! specified, all iterator parameters in this crate should yield elements in ascending order with
//! consecutive repeated elements removed. If this is upheld, then all iterators returned by this
//! crate will share those properties.

#[cfg(test)]
mod tests;

use std::cmp::{self, Ordering};
use std::fmt::{self, Debug};

/// Compare two sets represented by sorted, deduplicated iterators.
///
/// If the iterators are equal, then `Some(Equal)` is returned. If `a` is a subset of `b` then
/// `Some(Less)` is returned. If `a` is a superset of `b` then `Some(Greater)` is returned.
/// Otherwise, `None` is returned. If `a` and `b` are not sorted or contain duplicate values,
/// the return value is unspecified.
///
/// Time complexity: `O(a.len() + b.len())`.
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
/// See [`cmp`](fn.cmp.html).
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
/// See [`cmp`](fn.cmp.html).
pub fn cmp_by<T, L, R, F>(a: L, b: R, cmp: F) -> Option<Ordering>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).try_fold(Ordering::Equal, cmp_fold)
}

fn cmp_fold<T>(init: Ordering, (next, _): (Ordering, T)) -> Option<Ordering> {
    use Ordering::*;

    match (init, next) {
        (Less, Greater) | (Greater, Less) => None,
        (Equal, x) | (x, Equal) => Some(x),
        (Greater, Greater) => Some(Greater),
        (Less, Less) => Some(Less),
    }
}

/// Take the union of two sets represented by sorted, deduplicated iterators.
///
/// If an element is in both iterators, then only the one from `a` is yielded.
/// This behaviour can be overridden by using [`union_by`](fn.union_by.html).
///
/// Time complexity: `O(a.len() + b.len())`.
pub fn union<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).map(|(_, val)| val)
}

/// Take the union of two sets represented by sorted, deduplicated iterators, using a comparator
/// function.
///
/// Note that since this passes elements to the comparator function as `&mut T`, you can swap them
/// to override the default behaviour of returning duplicate elements from `a`.
///
/// See [`union`](fn.union.html).
pub fn union_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).map(|(_, val)| val)
}

/// Take the union of two sets represented by sorted, deduplicated iterators, using a key extraction
/// function.
///
/// See [`union`](fn.union.html).
pub fn union_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).map(|(_, val)| val)
}

/// Take the intersection of two sets represented by sorted, deduplicated iterators.
///
/// The elements returned will all be from `a`.
///
/// Time complexity: `O(a.len() + b.len())`.
pub fn intersection<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(intersection_filter)
}

/// Compare two sets represented by sorted, deduplicated iterators, using a comparator function.
///
/// See [`intersection`](fn.intersection.html).
pub fn intersection_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(intersection_filter)
}

/// Take the intersection of two sets represented by sorted, deduplicated iterators, using a key
/// extraction function.
///
/// See [`intersection`](fn.intersection.html).
pub fn intersection_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(intersection_filter)
}

fn intersection_filter<T>((src, val): (Ordering, T)) -> Option<T> {
    match src {
        Ordering::Equal => Some(val),
        Ordering::Greater | Ordering::Less => None,
    }
}

/// Take the difference of two sets (elements in `a` but not in `b`) represented by sorted,
/// deduplicated iterators.
///
/// Time complexity: `O(a.len() + b.len())`.
pub fn difference<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(difference_filter)
}

/// Compare two sets represented by sorted, deduplicated iterators, using a comparator function.
///
/// See [`difference`](fn.intersection.html).
pub fn difference_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(difference_filter)
}

/// Take the difference of two sets represented by sorted, deduplicated iterators, using a key
/// extraction function.
///
/// See [`difference`](fn.intersection.html).
pub fn difference_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(difference_filter)
}

fn difference_filter<T>((src, val): (Ordering, T)) -> Option<T> {
    match src {
        Ordering::Less | Ordering::Equal => None,
        Ordering::Greater => Some(val),
    }
}

/// Take the symmetric_difference of two sets represented by sorted, deduplicated iterators.
///
/// Time complexity: `O(a.len() + b.len())`.
pub fn symmetric_difference<T, L, R>(a: L, b: R) -> impl Iterator<Item = T>
where
    T: Ord,
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
{
    classify(a, b).filter_map(symmetric_difference_filter)
}

/// Compare two sets represented by sorted, deduplicated iterators, using a comparator function.
///
/// See [`symmetric_difference`](fn.intersection.html).
pub fn symmetric_difference_by<T, L, R, F>(a: L, b: R, cmp: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    F: FnMut(&mut T, &mut T) -> Ordering,
{
    classify_by(a, b, cmp).filter_map(symmetric_difference_filter)
}

/// Take the symmetric_difference of two sets represented by sorted, deduplicated iterators, using a
/// key extraction function.
///
/// See [`symmetric_difference`](fn.intersection.html).
pub fn symmetric_difference_by_key<T, L, R, K, F>(a: L, b: R, key: F) -> impl Iterator<Item = T>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by_key(a, b, key).filter_map(symmetric_difference_filter)
}

fn symmetric_difference_filter<T>((src, val): (Ordering, T)) -> Option<T> {
    match src {
        Ordering::Less | Ordering::Greater => Some(val),
        Ordering::Equal => None,
    }
}

/// Interleave two sorted, deduplicated iterators in sorted order and classify each element according
/// to its source:
/// * `Ordering::Less`: from `a`.
/// * `Ordering::Equal`: from both `a` and `b`. (The element from `a` is returned)
/// * `Ordering::Greater`: from `b`.
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
/// See [`classify`](fn.classify.html).
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
/// See [`classify`](fn.classify.html).
pub fn classify_by_key<T, L, R, K, F>(a: L, b: R, mut key: F) -> impl Iterator<Item = (Ordering, T)>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    K: Ord,
    F: FnMut(&T) -> K,
{
    classify_by(a, b, move |l, r| Ord::cmp(&key(l), &key(r)))
}

/// An iterator that interleaves two sorted, deduplicated iterators in sorted order and classifies
/// each element according to its source.
///
/// This `struct` is created by the [`classify`](fn.classify.html) function. See its documentation
/// for more.
pub struct Classify<L, R>
where
    L: Iterator,
    R: Iterator,
{
    lhs: Peekable<L>,
    rhs: Peekable<R>,
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
            lhs: Peekable::new(lhs.into_iter()),
            rhs: Peekable::new(rhs.into_iter()),
        }
    }

    fn next_by<F>(&mut self, mut cmp: F) -> Option<(Ordering, T)>
    where
        F: FnMut(&mut T, &mut T) -> Ordering,
    {
        use Ordering::*;

        let src = match (self.lhs.peek(), self.rhs.peek()) {
            (Some(l), Some(r)) => cmp(l, r).reverse(),
            (None, Some(_)) => Less,
            (Some(_), None) => Greater,
            (None, None) => return None,
        };

        let val = match src {
            Ordering::Greater => self.lhs.peek.take(),
            Ordering::Less => self.rhs.peek.take(),
            Ordering::Equal => {
                self.rhs.peek.take();
                self.lhs.peek.take()
            }
        };

        val.map(|v| (src, v))
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

impl<T, L, R> Iterator for Classify<L, R>
where
    T: Ord,
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = (Ordering, T);

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
/// This `struct` is created by the [`classify_by`] and [`classify_by_key`] functions. See their
/// documentation for more.
///
/// [`classify_by`]: fn.classify_by.html
/// [`classify_by_key`]: fn.classify_by_key.html
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
    type Item = (Ordering, T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next_by(&mut self.cmp)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

struct Peekable<I: Iterator> {
    iter: I,
    peek: Option<I::Item>,
}

impl<I: Iterator> Peekable<I> {
    fn new(iter: I) -> Self {
        Peekable { iter, peek: None }
    }

    fn peek(&mut self) -> Option<&mut I::Item> {
        if self.peek.is_none() {
            self.peek = self.iter.next();
        }
        self.peek.as_mut()
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
