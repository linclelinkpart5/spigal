use core::ops::{Index, IndexMut};

pub use crate::iter::*;

mod iter;

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
        let wrapped_index = self.lookup(index, true).unwrap();
        &self.buffer[wrapped_index]
    }

    /// Similar to [`Self::get_wrapped`], but returns a mutable reference instead.
    #[inline]
    pub fn get_wrapped_mut(&mut self, index: usize) -> &mut E {
        let wrapped_index = self.lookup(index, true).unwrap();
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

    use core::ops::RangeInclusive;

    use proptest::prelude::*;

    const MAX_BUF_LEN: usize = 100;
    const BUF_LEN_RANGE: RangeInclusive<usize> = 0..=MAX_BUF_LEN;

    const MAX_FEED_LEN: usize = 1000;
    const FEED_LEN_RANGE: RangeInclusive<usize> = 1..=MAX_FEED_LEN;

    fn arb_buf<T: Arbitrary>() -> impl Strategy<Value = Vec<T>> {
        prop::collection::vec(any::<T>(), BUF_LEN_RANGE)
    }

    fn arb_feed<T: Arbitrary>() -> impl Strategy<Value = Vec<T>> {
        prop::collection::vec(any::<T>(), FEED_LEN_RANGE)
    }

    proptest! {
        #[test]
        fn test_fill__basic(elem in any::<i32>(), mut raw_buf in arb_buf()) {
            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            ring_buf.fill(elem);

            assert!(ring_buf.buffer.iter().all(|e| e == &elem));
            assert_eq!(ring_buf.head, 0);
        }

        #[test]
        fn test_fill_with__basic(mut raw_buf in arb_buf()) {
            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            let mut i = 1u32;
            ring_buf.fill_with(|| { let r = i; i = i.rotate_left(1); r });

            let mut i = 1;
            assert!(ring_buf.buffer.iter().all(|e| { let b = e == &i; i = i.rotate_left(1); b }));
            assert_eq!(ring_buf.head, 0);
        }

        #[test]
        fn test_fill_with__not_clone(len in BUF_LEN_RANGE) {
            #[derive(Debug)]
            struct NotClone(u32);

            let mut raw_buf = Vec::with_capacity(len);
            for _ in 0..len {
                raw_buf.push(NotClone(0));
            }

            let mut ring_buf = RingBuffer::from(raw_buf.as_mut_slice());
            let mut i = 1u32;
            ring_buf.fill_with(|| {
                let r = i;
                i = i.rotate_left(1);
                NotClone(r)
            });

            let mut i = 1;
            assert!(ring_buf.buffer.iter().all(|NotClone(e)| { let b = e == &i; i = i.rotate_left(1); b }));
            assert_eq!(ring_buf.head, 0);
        }

        #[test]
        fn test_len__basic(mut raw_buf in arb_buf::<bool>()) {
            let expected_len = raw_buf.len();
            let ring_buf = RingBuffer::from(raw_buf.as_mut_slice());

            assert_eq!(ring_buf.len(), expected_len);
        }

        #[test]
        fn test_push__basic(mut raw_buf in arb_buf::<i32>(), start_index in any::<usize>(), feed in arb_feed()) {
            let offset = start_index.checked_rem(raw_buf.len()).unwrap_or(0);

            let expected = raw_buf[offset..].iter()
                .copied()
                .chain(
                    raw_buf[..offset].iter()
                    .copied()
                )
                .chain(
                    feed.iter()
                    .copied()
                )
                .take(feed.len())
                .collect::<Vec<_>>();

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), start_index);

            assert_eq!(ring_buf.head, offset);

            let produced = feed.into_iter().map(|e| {
                ring_buf.push(e)
            }).collect::<Vec<_>>();

            assert_eq!(produced, expected);
        }

        #[test]
        fn test_push_flagged__basic(mut raw_buf in arb_buf::<i32>(), start_index in any::<usize>(), feed in arb_feed()) {
            let offset = start_index.checked_rem(raw_buf.len()).unwrap_or(0);

            let mut i = offset;
            let n = raw_buf.len();
            let wrap_detector = core::iter::from_fn(|| {
                i = (i + 1).checked_rem(n).unwrap_or(0);

                Some(i == 0)
            });

            let expected = raw_buf[offset..].iter()
                .copied()
                .chain(
                    raw_buf[..offset].iter()
                    .copied()
                )
                .chain(
                    feed.iter()
                    .copied()
                )
                .take(feed.len())
                .zip(wrap_detector)
                .collect::<Vec<_>>();

            let mut ring_buf = RingBuffer::from_offset(raw_buf.as_mut_slice(), start_index);

            assert_eq!(ring_buf.head, offset);

            let produced = feed.into_iter().map(|e| {
                ring_buf.push_flagged(e)
            }).collect::<Vec<_>>();

            assert_eq!(produced, expected);
        }
    }
}
