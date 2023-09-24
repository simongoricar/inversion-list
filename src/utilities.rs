use std::ops::{Range, RangeBounds};

/// Converts any range (inclusive, open-ended, ...) into a "normal" half-open [`Range`].
/// Returns `None` if the range is empty (or the range unbounded, i.e. `..12`).
pub(crate) fn range_bounds_to_range<R, V>(range: R) -> Option<Range<V>>
where
    R: RangeBounds<V>,
    V: num::Integer + Clone,
{
    let range_start_inclusive = match range.start_bound() {
        std::ops::Bound::Included(start) => start.clone(),
        std::ops::Bound::Excluded(start_excluded) => {
            start_excluded.clone().add(V::one())
        }
        std::ops::Bound::Unbounded => return None,
    };

    let range_end_exclusive = match range.end_bound() {
        std::ops::Bound::Included(end_inclusive) => {
            end_inclusive.clone().add(V::one())
        }
        std::ops::Bound::Excluded(end) => end.clone(),
        std::ops::Bound::Unbounded => return None,
    };

    if range_start_inclusive >= range_end_exclusive {
        None
    } else {
        Some(range_start_inclusive..range_end_exclusive)
    }
}
