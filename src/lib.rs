use core::ops::{Index, IndexMut};

pub use crate::iter::*;

mod iter;

const NORMALIZE: bool = true;

pub struct RingBuffer<'b, E> {
    buffer: &'b mut [E],
    head: usize,
}

impl<'b, E> RingBuffer<'b, E> {
    /// Sets all values of this buffer using a given closure, and sets the head
    /// index to 0.
    pub fn fill_with<F>(&mut self, func: F)
    where
        F: FnMut() -> E,
    {
        self.buffer.fill_with(func);
        self.head = 0;
    }

    /// Sets all values of this buffer by feeding in an iterator. Returns `Ok`
    /// if there were enough elements in the iterator to exactly fill the
    /// buffer once, `Err(c)` otherwise, where `c` is the number of elements
    /// that were read and pushed into the buffer. Note that `c` will always be
    /// less than the length of the buffer.
    pub fn fill_iter<I>(&mut self, iter: I) -> Result<(), usize>
    where
        I: IntoIterator<Item = E>,
    {
        if NORMALIZE {
            self.buffer.rotate_left(self.head);
            self.head = 0;
        }

        let mut iter = iter.into_iter();

        for c in 0..self.len() {
            if let Some(elem) = iter.next() {
                self.push(elem);
            } else {
                return Err(c);
            }
        }

        Ok(())
    }

    /// Returns the length of this buffer.
    #[inline]
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Pushes a new element onto the rear of the buffer, and pops off and
    /// returns the replaced element from the front.
    pub fn push(&mut self, elem: E) -> E {
        let (popped, _) = self.push_flagged(elem);
        popped
    }

    /// Pushes a new element onto the rear of the buffer, and pops off and
    /// returns the replaced element from the front, along with a boolean flag
    /// indicating if the new pushed element caused the head index to wrap
    /// around to the start of the buffer.
    pub fn push_flagged(&mut self, elem: E) -> (E, bool) {
        if self.len() == 0 {
            // Buffer has zero capacity, just re-return the passed-in element.
            return (elem, true);
        }

        // Calculate the next head position after this push.
        let mut was_reset = false;
        let mut next_head = self.head + 1;
        if next_head >= self.len() {
            next_head = 0;
            was_reset = true;
        }

        // SAFETY: Bounds checking can be skipped since the length is constant.
        let old_elem =
            unsafe { core::mem::replace(self.buffer.get_unchecked_mut(self.head), elem) };
        self.head = next_head;
        (old_elem, was_reset)
    }

    /// Helper method to wrap (or not) indices.
    #[inline]
    fn lookup(&self, index: usize, wrap: bool) -> Option<usize> {
        if !wrap && index >= self.len() {
            None
        } else {
            let c = self.len();
            if c == 0 {
                None
            } else {
                Some((self.head + (index % c)) % c)
            }
        }
    }

    /// Returns a reference to the element at the given index, or [`None`] if
    /// out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&E> {
        let wrapped_index = self.lookup(index, false)?;
        self.buffer.get(wrapped_index)
    }

    /// Similar to [`Self::get`], but returns a mutable reference instead.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut E> {
        let wrapped_index = self.lookup(index, false)?;
        self.buffer.get_mut(wrapped_index)
    }

    /// Returns a reference to the element at the given index, wrapping around
    /// the length of the buffer if needed. Panics if the buffer has a capacity
    /// of 0.
    #[inline]
    pub fn get_wrapped(&self, index: usize) -> &E {
        let wrapped_index = self
            .lookup(index, true)
            .expect("index out of bounds: the len is 0");
        &self.buffer[wrapped_index]
    }

    /// Similar to [`Self::get_wrapped`], but returns a mutable reference instead.
    #[inline]
    pub fn get_wrapped_mut(&mut self, index: usize) -> &mut E {
        let wrapped_index = self
            .lookup(index, true)
            .expect("index out of bounds: the len is 0");
        &mut self.buffer[wrapped_index]
    }

    /// Constructs a new ring buffer from a given inner buffer and
    /// starting index.
    ///
    /// This method should only be used if you require specifying a first index.
    /// For most use cases, it is better to use [`Self::from`] instead.
    #[inline]
    pub fn from_offset(buffer: &'b mut [E], head: usize) -> Self {
        let wrapped_head = head.checked_rem(buffer.as_ref().len()).unwrap_or(0);

        Self {
            head: wrapped_head,
            buffer,
        }
    }

    /// Decomposes this ring buffer into a head index and inner buffer.
    #[inline]
    pub fn into_raw_parts(self) -> (usize, &'b mut [E]) {
        let Self { head, buffer } = self;
        (head, buffer)
    }

    fn as_slices(&self) -> (&[E], &[E]) {
        let (tail, head) = self.buffer.split_at(self.head);
        (head, tail)
    }

    fn as_slices_mut(&mut self) -> (&mut [E], &mut [E]) {
        let (tail, head) = self.buffer.split_at_mut(self.head);
        (head, tail)
    }

    /// Returns an iterator that yields references to the items in this buffer,
    /// in order.
    pub fn iter(&self) -> Iter<'_, E> {
        let (head, tail) = self.as_slices();

        Iter {
            head: head.iter(),
            tail: tail.iter(),
        }
    }

    /// Similar to [`Self::iter`], but with mutable references instead.
    pub fn iter_mut(&mut self) -> IterMut<'_, E> {
        let (head, tail) = self.as_slices_mut();

        IterMut {
            head: head.iter_mut(),
            tail: tail.iter_mut(),
        }
    }
}

impl<'b, E: Clone> RingBuffer<'b, E> {
    /// Sets all values of this buffer to a given value, and sets the head
    /// index to 0.
    pub fn fill(&mut self, elem: E) {
        self.buffer.fill(elem);
        self.head = 0;
    }
}

impl<'b, E> From<&'b mut [E]> for RingBuffer<'b, E> {
    /// Constructs a new ring buffer from a given inner buffer.
    fn from(buffer: &'b mut [E]) -> Self {
        Self::from_offset(buffer, 0)
    }
}

impl<'b, E> Index<usize> for RingBuffer<'b, E> {
    type Output = E;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get_wrapped(index)
    }
}

impl<'b, E> IndexMut<usize> for RingBuffer<'b, E> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_wrapped_mut(index)
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use super::*;

    use std::collections::VecDeque;

    use proptest::prelude::*;

    #[repr(usize)]
    enum Size {
        M = 100,
        L = 1000,
    }

    enum Empty {
        OK,
        Non,
    }

    fn arb_values<T: Arbitrary>(size: Size, empty: Empty) -> impl Strategy<Value = Vec<T>> {
        let lower_bound = match empty {
            Empty::OK => 0,
            Empty::Non => 1,
        };

        prop::collection::vec(any::<T>(), lower_bound..(size as usize))
    }

    proptest! {
        #[test]
        fn test_fill__basic(elem in any::<i32>(), mut raw_buf in arb_values(Size::M, Empty::OK)) {
            let expected_contents = vec![elem; raw_buf.len()];

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            ring_buf.fill(elem);

            let produced_contents = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_contents, expected_contents);
        }

        #[test]
        fn test_fill_with__basic(mut raw_buf in arb_values(Size::M, Empty::OK)) {
            let mut expected_contents = Vec::with_capacity(raw_buf.len());

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            let mut i = 1u32;
            ring_buf.fill_with(|| { let r = i; i = i.rotate_left(1); expected_contents.push(r); r });

            let produced_contents = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_contents, expected_contents);
        }

        #[test]
        fn test_fill_with__not_clone(len in 0..=(Size::M as usize)) {
            #[derive(Debug, PartialEq)]
            struct NotClone(u32);

            let mut raw_buf = Vec::with_capacity(len);
            for _ in 0..len {
                raw_buf.push(NotClone(0));
            }

            let mut expected_contents = Vec::with_capacity(len);

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            let mut i = 1u32;
            ring_buf.fill_with(|| {
                let r = i;
                i = i.rotate_left(1);
                expected_contents.push(NotClone(r));
                NotClone(r)
            });

            let produced_contents = ring_buf.iter().map(|&NotClone(i)| NotClone(i)).collect::<Vec<_>>();

            assert_eq!(produced_contents, expected_contents);
        }

        #[test]
        fn test_fill_iter__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), feed in arb_values::<i32>(Size::L, Empty::OK)) {
            let expected_result = match feed.len().checked_sub(raw_buf.len()) {
                None => Err(feed.len()),
                Some(..) => Ok(()),
            };

            let orig_raw_buf = raw_buf.clone();

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            let produced_result = ring_buf.fill_iter(feed.iter().copied());

            assert_eq!(produced_result, expected_result);

            let to_skip = match expected_result {
                Err(c) => c,
                Ok(()) => orig_raw_buf.len(),
            };
            let expected_contents = orig_raw_buf.into_iter().skip(to_skip).chain(feed.iter().copied().take(to_skip)).collect::<Vec<_>>();
            let produced_contents = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_contents, expected_contents);
        }

        #[test]
        fn test_len__basic(mut raw_buf in arb_values::<bool>(Size::L, Empty::OK)) {
            let expected_len = raw_buf.len();
            let ring_buf = RingBuffer::from(raw_buf.as_mut_slice());

            assert_eq!(ring_buf.len(), expected_len);
        }

        #[test]
        fn test_push__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), feed in arb_values(Size::L, Empty::Non)) {
            let mut reference_state = VecDeque::from(raw_buf.clone());

            let expected_returns = raw_buf.iter()
                .copied()
                .chain(
                    feed.iter()
                    .copied()
                )
                .take(feed.len())
                .collect::<Vec<_>>();

            let mut produced_returns = Vec::with_capacity(feed.len());

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());

            for elem in feed {
                let produced_return = ring_buf.push(elem);
                produced_returns.push(produced_return);

                // Update and assert reference state.
                reference_state.push_back(elem);
                reference_state.pop_front().unwrap();

                let expected_state = reference_state.iter().copied().collect::<Vec<_>>();
                let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

                assert_eq!(produced_state, expected_state);
            }

            assert_eq!(produced_returns, expected_returns);
        }

        #[test]
        fn test_push_flagged__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), feed in arb_values(Size::L, Empty::Non)) {
            let mut reference_state = VecDeque::from(raw_buf.clone());

            let mut i = 0usize;
            let n = raw_buf.len();
            let wrap_detector = core::iter::from_fn(|| {
                i = (i + 1).checked_rem(n).unwrap_or(0);

                Some(i == 0)
            });

            let expected_returns = raw_buf.iter()
                .copied()
                .chain(
                    feed.iter()
                    .copied()
                )
                .take(feed.len())
                .zip(wrap_detector)
                .collect::<Vec<_>>();

            let mut produced_returns = Vec::with_capacity(feed.len());

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());

            for elem in feed {
                let produced_return = ring_buf.push_flagged(elem);
                produced_returns.push(produced_return);

                // Update and assert reference state.
                reference_state.push_back(elem);
                reference_state.pop_front().unwrap();

                let expected_state = reference_state.iter().copied().collect::<Vec<_>>();
                let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

                assert_eq!(produced_state, expected_state);
            }

            assert_eq!(produced_returns, expected_returns);
        }

        #[test]
        fn test_get__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), offset in any::<usize>()) {
            const EXTRA_LOOKAHEAD: usize = 16;

            let offset = offset.checked_rem(raw_buf.len()).unwrap_or(0);

            let mut reference_state = raw_buf.clone();
            reference_state.rotate_left(offset);

            let expected_returns = (0..raw_buf.len() + EXTRA_LOOKAHEAD).map(|i| reference_state.get(i).copied()).collect::<Vec<_>>();

            let ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len() + EXTRA_LOOKAHEAD).map(|i| ring_buf.get(i).copied()).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);
        }

        #[test]
        fn test_get_mut__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), offset in any::<usize>()) {
            const EXTRA_LOOKAHEAD: usize = 16;

            fn mutator(i: &mut i32) -> i32 {
                let r = *i;
                *i = !*i;
                r
            }

            let offset = offset.checked_rem(raw_buf.len()).unwrap_or(0);

            let mut reference_state = raw_buf.clone();
            reference_state.rotate_left(offset);

            let expected_returns = (0..raw_buf.len() + EXTRA_LOOKAHEAD).map(|i| reference_state.get_mut(i).map(mutator)).collect::<Vec<_>>();

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len() + EXTRA_LOOKAHEAD).map(|i| ring_buf.get_mut(i).map(mutator)).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);

            let expected_state = reference_state;
            let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_state, expected_state);
        }

        #[test]
        fn test_get_wrapped__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::Non), offset in any::<usize>()) {
            const EXTRA_LOOKAHEAD: usize = 16;

            let offset = offset.checked_rem(raw_buf.len()).unwrap_or(0);

            let mut reference_state = raw_buf.clone();
            reference_state.rotate_left(offset);

            let expected_returns = (0..raw_buf.len() + EXTRA_LOOKAHEAD).map(|i| reference_state[i % raw_buf.len()]).collect::<Vec<_>>();

            let ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len() + EXTRA_LOOKAHEAD).map(|i| *ring_buf.get_wrapped(i)).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);
        }
    }
}
