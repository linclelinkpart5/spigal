#[inline]
pub(super) fn lookup(
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
        }
}
