#[inline]
pub(super) fn mod_cycle_offset(
    head: usize,
    len: usize,
    offset: usize,
    forward: bool,
    allow_rewrap: bool,
) -> Option<usize> {
    debug_assert!((len > 0 && head < len) || (len == 0 && head == 0));

    // An empty buffer can never have a valid index.
    if len == 0 {
        None
    }
    // If re-wrapping is disabled, the offset must be in bounds in order to
    // produce a valid index.
    else if !allow_rewrap && offset >= len {
        None
    }
    // Re-wrap the offset as many times as needed around the head origin.
    else {
        // NOTE: This is a little convoluted, but avoids any overflow (i.e.
        //       if `a + b` could overflow in `(a + b) % n`).
        let mod_offset = offset % len;

        if mod_offset == 0 {
            // No-op, no work needed.
            Some(head)
        } else {
            let b = if forward {
                mod_offset
            } else {
                // Offsetting `n` spaces backward is equivalent to offsetting
                // `len - n` spaces forward.
                len - mod_offset
            };

            let z = len - head;

            let d = if b >= z { b - z } else { head + b };
            debug_assert!(d < len);

            Some(d)
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use super::*;

    use proptest::prelude::*;

    fn arb_head_len_offset() -> impl Strategy<Value = (usize, usize, usize)> {
        (1usize..=10000).prop_flat_map(move |len| ((0..len), Just(len), 0..(len * 2)))
    }

    proptest! {
    #[test]
    fn test_mod_cycle_offset__non_empty_exhaustive((head, len, offset) in arb_head_len_offset(), forward in any::<bool>(), allow_rewrap in any::<bool>()) {
        let produced = mod_cycle_offset(head, len, offset, forward, allow_rewrap);

        let expected = if !allow_rewrap && offset >= len {
            // If wrapping is disabled, the non-normalized offset must be
            // in the interval [0, len).
            None
        }
        else {
            let mod_offset = offset % len;

            let fwd_offset = if forward {
                mod_offset
            } else {
                len - mod_offset
            };

            Some((head + fwd_offset) % len)
        };

        assert_eq!(produced, expected);
    }

    #[test]
    fn test_mod_cycle_offset__empty_exhaustive(offset in any::<usize>(), forward in any::<bool>(), allow_rewrap in any::<bool>()) {
        let produced = mod_cycle_offset(0, 0, offset, forward, allow_rewrap);
        let expected = None;

        assert_eq!(produced, expected);
    }
        }
}
