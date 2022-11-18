use core::iter::FusedIterator;
use core::ops::{Index, IndexMut};
use core::slice::{Iter as SliceIter, IterMut as SliceIterMut};

pub struct RingBuffer<'b, E: Copy + PartialEq> {
    buffer: &'b mut [E],
    head: usize,
}

impl<'b, E: Copy + PartialEq> RingBuffer<'b, E> {
    /// Sets all values of this buffer to a given value, and sets the head
    /// index to 0.
    pub fn fill(&mut self, elem: E) {
        self.buffer.fill(elem);
        self.head = 0;
    }

    /// Sets all values of this buffer using a given closure, and sets the head
    /// index to 0.
    pub fn fill_with<F>(&mut self, func: F)
    where
        F: FnMut() -> E,
    {
        self.buffer.fill_with(func);
        self.head = 0;
    }

    /// Returns the maximum number of elements this buffer can contain.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    /// Helper method to push new elements.
    pub(crate) fn push_with_flag(&mut self, elem: E) -> (E, bool) {
        if self.capacity() == 0 {
            // Buffer has zero capacity, just re-return the passed-in element.
            return (elem, true);
        }

        // Calculate the next head position after this push.
        let mut was_reset = false;
        let mut next_head = self.head + 1;
        if next_head >= self.capacity() {
            next_head = 0;
            was_reset = true;
        }

        // SAFETY: Bounds checking can be skipped since the length is constant.
        let old_elem =
            unsafe { core::mem::replace(self.buffer.get_unchecked_mut(self.head), elem) };
        self.head = next_head;
        (old_elem, was_reset)
    }

    /// Pushes a new element onto the rear of the buffer, and pops off and
    /// returns the replaced element from the front.
    pub fn push(&mut self, elem: E) -> E {
        let (popped, _) = self.push_with_flag(elem);
        popped
    }

    /// Helper method to wrap (or not) indices.
    #[inline]
    fn lookup(&self, index: usize, wrap: bool) -> Option<usize> {
        if !wrap && index >= self.capacity() {
            None
        } else {
            let c = self.capacity();
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
        &mut self.buffer.as_mut()[wrapped_index]
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

impl<'b, E: Copy + PartialEq> From<&'b mut [E]> for RingBuffer<'b, E> {
    /// Constructs a new ring buffer from a given inner buffer.
    fn from(buffer: &'b mut [E]) -> Self {
        Self::from_offset(buffer, 0)
    }
}

impl<'b, E: Copy + PartialEq> Index<usize> for RingBuffer<'b, E> {
    type Output = E;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get_wrapped(index)
    }
}

impl<'b, E: Copy + PartialEq> IndexMut<usize> for RingBuffer<'b, E> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.get_wrapped_mut(index)
    }
}

#[derive(Clone)]
pub struct Iter<'a, I> {
    head: SliceIter<'a, I>,
    tail: SliceIter<'a, I>,
}

impl<'a, I> Iterator for Iter<'a, I> {
    type Item = &'a I;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.next().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
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

impl<'a, I> ExactSizeIterator for Iter<'a, I> {
    fn len(&self) -> usize {
        self.head.len() + self.tail.len()
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

impl<'a, I> FusedIterator for Iter<'a, I> {}

pub struct IterMut<'a, I> {
    head: SliceIterMut<'a, I>,
    tail: SliceIterMut<'a, I>,
}

impl<'a, I> Iterator for IterMut<'a, I> {
    type Item = &'a mut I;

    fn next(&mut self) -> Option<Self::Item> {
        self.head.next().or_else(|| self.tail.next())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
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

impl<'a, I> ExactSizeIterator for IterMut<'a, I> {
    fn len(&self) -> usize {
        self.head.len() + self.tail.len()
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

impl<'a, I> FusedIterator for IterMut<'a, I> {}
