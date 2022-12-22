#![cfg_attr(not(test), no_std)]

use core::ops::{Index, IndexMut};

pub use crate::iter::*;

mod iter;

const EMPTY_BUFFER_ERR: &str = "buffer should have a len greater than 0";

fn lookup(
    head: usize,
    len: usize,
    offset: usize,
    forward: bool,
    allow_wrap: bool,
) -> Option<usize> {
    debug_assert!((len > 0 && head < len) || (len == 0 && head == 0));

    if len == 0 {
        // An empty buffer can never have a valid index.
        None
    } else if !allow_wrap && offset >= len {
        // If wrapping is disabled, the offset must be in bounds in order to
        // produce a valid index.
        None
    } else {
        // NOTE: This is a little convoluted, but avoids any overflow (i.e.
        //       if `a + b` could overflow in `(a + b) % n`).
        let norm_offset = offset % len;

        if norm_offset == 0 {
            // No-op, no work needed.
            Some(head)
        } else {
            let b = if forward {
                norm_offset
            } else {
                len - norm_offset
            };

            let z = len - head;

            let d = if b >= z { b - z } else { head + b };
            debug_assert!(d < len);

            Some(d)
        }
    }
}

fn tail_index(head: usize, len: usize) -> Option<usize> {
    lookup(head, len, 1, false, true)
}

pub struct RingBuffer<'b, E> {
    buffer: &'b mut [E],
    head: usize,
}

impl<'b, E> RingBuffer<'b, E> {
    /// Sets all values of this buffer using a given closure.
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
        let mut iter = iter.into_iter();

        for c in 0..self.len() {
            if let Some(elem) = iter.next() {
                self.push_back(elem);
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

    /// Helper method to perform cyclic rotations. Since this is a ring buffer,
    /// these rotation operations just involve shifting the head index, and are
    /// very efficient.
    fn rotate(&mut self, n: usize, forward: bool) {
        lookup(self.head, self.len(), n, forward, true).map(|i| self.head = i);
    }

    /// Rotates the ring buffer `n` elements to the left. This has the same
    /// effect as popping the front element and pushing it onto the back of the
    /// ring buffer, repeated `n` times.
    pub fn rotate_left(&mut self, n: usize) {
        self.rotate(n, true)
    }

    /// Rotates the ring buffer `n` elements to the right. This has the same
    /// effect as popping the back element and pushing it onto the front of the
    /// ring buffer, repeated `n` times.
    pub fn rotate_right(&mut self, n: usize) {
        self.rotate(n, false)
    }

    /// Helper method to assist with push-popping from either end of the ring
    /// buffer.
    fn push_pop(&mut self, elem: E, to_front: bool) -> E {
        if self.len() == 0 {
            // Buffer has zero capacity, just re-return the passed-in element.
            return elem;
        }

        if to_front {
            self.rotate_right(1);
        }

        debug_assert!(self.head < self.buffer.len());
        let old_elem =
            unsafe { core::mem::replace(self.buffer.get_unchecked_mut(self.head), elem) };

        if !to_front {
            self.rotate_left(1);
        }

        old_elem
    }

    /// Pushes a new element onto the back of the buffer, and pops off and
    /// returns the replaced element from the front.
    pub fn push_back(&mut self, elem: E) -> E {
        self.push_pop(elem, false)
    }

    /// Pushes a new element onto the front of the buffer, and pops off and
    /// returns the replaced element from the back.
    pub fn push_front(&mut self, elem: E) -> E {
        self.push_pop(elem, true)
    }

    /// Returns a reference to the element at the given index, or [`None`] if
    /// out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&E> {
        let wrapped_index = lookup(self.head, self.len(), index, true, false)?;
        self.buffer.get(wrapped_index)
    }

    /// Similar to [`Self::get`], but returns a mutable reference instead.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut E> {
        let wrapped_index = lookup(self.head, self.len(), index, true, false)?;
        self.buffer.get_mut(wrapped_index)
    }

    /// Returns a reference to the element at the given index, wrapping around
    /// the length of the buffer if needed. Panics if the buffer has a length
    /// of 0.
    #[inline]
    pub fn get_wrapped(&self, index: usize) -> &E {
        let wrapped_index =
            lookup(self.head, self.len(), index, true, true).expect(EMPTY_BUFFER_ERR);
        &self.buffer[wrapped_index]
    }

    /// Similar to [`Self::get_wrapped`], but returns a mutable reference instead.
    #[inline]
    pub fn get_wrapped_mut(&mut self, index: usize) -> &mut E {
        let wrapped_index =
            lookup(self.head, self.len(), index, true, true).expect(EMPTY_BUFFER_ERR);
        &mut self.buffer[wrapped_index]
    }

    /// Returns a reference to the element at the front of the ring buffer.
    /// Panics if the buffer has a length of 0.
    #[inline]
    pub fn front(&self) -> &E {
        self.buffer.get(self.head).expect(EMPTY_BUFFER_ERR)
    }

    /// Similar to [`Self::front`], but returns a mutable reference instead.
    #[inline]
    pub fn front_mut(&mut self) -> &mut E {
        self.buffer.get_mut(self.head).expect(EMPTY_BUFFER_ERR)
    }

    /// Returns a reference to the element at the back of the ring buffer.
    /// Panics if the buffer has a length of 0.
    #[inline]
    pub fn back(&self) -> &E {
        let ti = tail_index(self.head, self.buffer.len()).expect(EMPTY_BUFFER_ERR);
        &self.buffer[ti]
    }

    /// Similar to [`Self::back`], but returns a mutable reference instead.
    #[inline]
    pub fn back_mut(&mut self) -> &mut E {
        let ti = tail_index(self.head, self.buffer.len()).expect(EMPTY_BUFFER_ERR);
        &mut self.buffer[ti]
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

    /// Decomposes this ring buffer into the inner buffer and the current head
    /// index.
    #[inline]
    pub fn into_raw_parts(self) -> (&'b mut [E], usize) {
        let Self { head, buffer } = self;
        (buffer, head)
    }

    /// Returns the contents of the inner buffer as two slices: the first one
    /// is the head of the ring buffer, and the second is the tail.
    ///
    /// Iterating over all of the elements in the head slice, followed by all
    /// of the elements in the tail slice, will yield the elements in the ring
    /// buffer in order (as given by [`Self::iter`]).
    pub fn as_slices(&self) -> (&[E], &[E]) {
        let (tail, head) = self.buffer.split_at(self.head);
        (head, tail)
    }

    /// Similar to [`Self::as_slices`], but returns mutable slices instead.
    pub fn as_slices_mut(&mut self) -> (&mut [E], &mut [E]) {
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

    use cool_asserts::assert_panics;
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

    fn arb_head_len_offset() -> impl Strategy<Value = (usize, usize, usize)> {
        (1usize..=10000).prop_flat_map(move |len| ((0..len), Just(len), 0..(len * 2)))
    }

    proptest! {
        #[test]
        fn test_lookup__non_empty_exhaustive((head, len, offset) in arb_head_len_offset(), forward in any::<bool>(), allow_wrap in any::<bool>()) {
            let produced = lookup(head, len, offset, forward, allow_wrap);

            let norm_offset = offset % len;

            let expected = if !allow_wrap && offset >= len {
                // If wrapping is disabled, the non-normalized offset must be
                // in the interval [0, len).
                None
            }
            else {
                let x =
                    if forward {
                        (head + norm_offset) % len
                    } else {
                        if head >= norm_offset {
                            head - norm_offset
                        } else {
                            len - (norm_offset - head)
                        }
                    };

                Some(x)
            };

            assert_eq!(produced, expected);
        }

        #[test]
        fn test_lookup__empty_exhaustive(offset in any::<usize>(), forward in any::<bool>(), allow_wrap in any::<bool>()) {
            let produced = lookup(0, 0, offset, forward, allow_wrap);
            let expected = None;

            assert_eq!(produced, expected);
        }

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
        fn test_rotate_left__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), offset in any::<usize>(), n in any::<usize>()) {
            let mut expected_state = raw_buf.clone();

            // Match the state to the newly-created ring buffer.
            expected_state.rotate_left(offset.checked_rem(raw_buf.len()).unwrap_or(0));

            // Rotate state to the left to match the end ring buffer state.
            expected_state.rotate_left(n.checked_rem(raw_buf.len()).unwrap_or(0));

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            ring_buf.rotate_left(n);

            let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_state, expected_state);
        }

        #[test]
        fn test_rotate_right__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), offset in any::<usize>(), n in any::<usize>()) {
            let mut expected_state = raw_buf.clone();

            // Match the state to the newly-created ring buffer.
            expected_state.rotate_left(offset.checked_rem(raw_buf.len()).unwrap_or(0));

            // Rotate state to the right to match the end ring buffer state.
            expected_state.rotate_right(n.checked_rem(raw_buf.len()).unwrap_or(0));

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            ring_buf.rotate_right(n);

            let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_state, expected_state);
        }

        #[test]
        fn test_push_back__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), feed in arb_values(Size::L, Empty::Non)) {
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
                let produced_return = ring_buf.push_back(elem);
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
        fn test_push_front__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::OK), feed in arb_values(Size::L, Empty::Non)) {
            let mut reference_state = VecDeque::from(raw_buf.clone());

            let expected_returns = raw_buf.iter()
                .rev()
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
                let produced_return = ring_buf.push_front(elem);
                produced_returns.push(produced_return);

                // Update and assert reference state.
                reference_state.push_front(elem);
                reference_state.pop_back().unwrap();

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

        #[test]
        fn test_get_wrapped__empty(index in any::<usize>()) {
            let mut raw_buf = vec![0i32; 0];

            let ring_buf = RingBuffer::from(raw_buf.as_mut_slice());

            assert_panics!(
                ring_buf.get_wrapped(index),
                includes(EMPTY_BUFFER_ERR),
            )
        }

        #[test]
        fn test_get_wrapped_mut__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::Non), offset in any::<usize>()) {
            const EXTRA_LOOKAHEAD: usize = 16;

            fn mutator(i: &mut i32) -> i32 {
                let r = *i;
                *i = !*i;
                r
            }

            let offset = offset.checked_rem(raw_buf.len()).unwrap_or(0);

            let mut reference_state = raw_buf.clone();
            reference_state.rotate_left(offset);

            let expected_returns = (0..raw_buf.len() + EXTRA_LOOKAHEAD).map(|i| mutator(&mut reference_state[i % raw_buf.len()])).collect::<Vec<_>>();

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len() + EXTRA_LOOKAHEAD).map(|i| mutator(ring_buf.get_wrapped_mut(i))).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);

            let expected_state = reference_state;
            let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_state, expected_state);
        }

        #[test]
        fn test_front__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::Non), offset in any::<usize>()) {
            let mut expected_returns = raw_buf.clone();
            expected_returns.rotate_left(offset.checked_rem(raw_buf.len()).unwrap_or(0));

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len()).map(|_| {
                let r = *ring_buf.front();
                ring_buf.rotate_left(1);
                r
            }).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);
        }

        #[test]
        fn test_front_mut__basic(mut raw_buf in arb_values::<i32>(Size::M, Empty::Non), offset in any::<usize>()) {
            fn mutator(i: &mut i32) -> i32 {
                let r = *i;
                *i = !*i;
                r
            }

            let mut expected_returns = raw_buf.clone();
            expected_returns.rotate_left(offset.checked_rem(raw_buf.len()).unwrap_or(0));

            let mut expected_state = expected_returns.clone();
            expected_state.iter_mut().for_each(|e| { mutator(e); });

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), offset);

            let produced_returns = (0..ring_buf.len()).map(|_| {
                let r = mutator(ring_buf.front_mut());
                ring_buf.rotate_left(1);
                r
            }).collect::<Vec<_>>();

            assert_eq!(produced_returns, expected_returns);

            let produced_state = ring_buf.iter().copied().collect::<Vec<_>>();

            assert_eq!(produced_state, expected_state);
        }
    }
}
