use core::fmt;

pub(crate) struct PutBack<I: Iterator> {
    iter: I,
    next: Option<I::Item>,
}

impl<I: Iterator> PutBack<I> {
    pub fn new(iter: I) -> Self {
        PutBack { iter, next: None }
    }

    pub fn put_back(&mut self, item: I::Item) {
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.iter.size_hint();
        if self.next.is_some() {
            (
                lower.saturating_add(1),
                upper.and_then(|n| n.checked_add(1)),
            )
        } else {
            (lower, upper)
        }
    }
}

impl<I: fmt::Debug + Iterator> fmt::Debug for PutBack<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PutBack")
            .field("iter", &self.iter)
            .field(
                "next",
                if self.next.is_some() {
                    &"Some(_)"
                } else {
                    &"None"
                },
            )
            .finish()
    }
}
