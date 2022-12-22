use core::iter::FusedIterator;
use core::slice::{Iter as SliceIter, IterMut as SliceIterMut};

#[derive(Clone)]
pub struct Iter<'a, I> {
    pub(crate) head: SliceIter<'a, I>,
    pub(crate) tail: SliceIter<'a, I>,
}

impl<'a, I> Iterator for Iter<'a, I> {
    type Item = &'a I;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.next().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.head.len() + self.tail.len();
        (len, Some(len))
    }

    #[cfg(feature = "iter_advance_by")]
    fn advance_by(&mut self, n: usize) -> Result<(), usize> {
        match self.head.advance_by(n) {
            Ok(()) => Ok(()),
            Err(h_amt) => match self.tail.advance_by(n - h_amt) {
                Ok(()) => Ok(()),
                Err(t_amt) => Err(h_amt + t_amt),
            },
        }
    }
}

impl<'a, I> DoubleEndedIterator for Iter<'a, I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail.next_back().or_else(|| self.head.next_back())
    }

    #[cfg(feature = "iter_advance_by")]
    fn advance_back_by(&mut self, n: usize) -> Result<(), usize> {
        match self.tail.advance_back_by(n) {
            Ok(()) => Ok(()),
            Err(t_amt) => match self.head.advance_back_by(n - t_amt) {
                Ok(()) => Ok(()),
                Err(h_amt) => Err(h_amt + t_amt),
            },
        }
    }
}

impl<'a, I> ExactSizeIterator for Iter<'a, I> {}
impl<'a, I> FusedIterator for Iter<'a, I> {}

pub struct IterMut<'a, I> {
    pub(crate) head: SliceIterMut<'a, I>,
    pub(crate) tail: SliceIterMut<'a, I>,
}

impl<'a, I> Iterator for IterMut<'a, I> {
    type Item = &'a mut I;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.next().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.head.len() + self.tail.len();
        (len, Some(len))
    }

    #[cfg(feature = "iter_advance_by")]
    fn advance_by(&mut self, n: usize) -> Result<(), usize> {
        match self.head.advance_by(n) {
            Ok(()) => Ok(()),
            Err(h_amt) => match self.tail.advance_by(n - h_amt) {
                Ok(()) => Ok(()),
                Err(t_amt) => Err(h_amt + t_amt),
            },
        }
    }
}

impl<'a, I> DoubleEndedIterator for IterMut<'a, I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail.next_back().or_else(|| self.head.next_back())
    }

    #[cfg(feature = "iter_advance_by")]
    fn advance_back_by(&mut self, n: usize) -> Result<(), usize> {
        match self.tail.advance_back_by(n) {
            Ok(()) => Ok(()),
            Err(t_amt) => match self.head.advance_back_by(n - t_amt) {
                Ok(()) => Ok(()),
                Err(h_amt) => Err(h_amt + t_amt),
            },
        }
    }
}

impl<'a, I> ExactSizeIterator for IterMut<'a, I> {}
impl<'a, I> FusedIterator for IterMut<'a, I> {}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use super::*;

    use proptest::prelude::*;

    const MAX_SIDE_LEN: usize = 100;

    fn arb_head_tail() -> impl Strategy<Value = (Vec<i32>, Vec<i32>)> {
        (
            proptest::collection::vec(any::<i32>(), 0..=MAX_SIDE_LEN),
            proptest::collection::vec(any::<i32>(), 0..=MAX_SIDE_LEN),
        )
    }

    proptest! {
        #[test]
        fn test_iter__forward_order((head, tail) in arb_head_tail()) {
            let expected_iteration = head.iter().copied().chain(tail.iter().copied()).collect::<Vec<_>>();

            let iter = Iter {
                head: head.iter(),
                tail: tail.iter(),
            };

            let produced_iteration = iter.copied().collect::<Vec<_>>();

            assert_eq!(produced_iteration, expected_iteration);
        }

        #[test]
        fn test_iter__reverse_order((head, tail) in arb_head_tail()) {
            let expected_iteration = tail.iter().rev().copied().chain(head.iter().rev().copied()).collect::<Vec<_>>();

            let iter = Iter {
                head: head.iter(),
                tail: tail.iter(),
            };

            let produced_iteration = iter.rev().copied().collect::<Vec<_>>();

            assert_eq!(produced_iteration, expected_iteration);
        }
    }
}
