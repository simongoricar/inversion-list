use std::{
    cmp::Ordering,
    collections::VecDeque,
    ops::{Range, RangeBounds},
};

use crate::{
    error::{InsertError, LookupError},
    iter::{InversionMapIntoIter, InversionMapIter, InversionMapMutIter},
    utilities::range_bounds_to_range,
};


/// A single inversion list entry.
///
/// Numeric range is of type `R` (must implement [`num::Integer`](../num/trait.Integer.html)` + `[`Copy`])
/// and the associated value is of type `V` (must implement [`Clone`]).
#[derive(Clone, Debug)]
pub struct InversionEntry<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    range: Range<R>,
    value: V,
}

impl<R, V> InversionEntry<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    #[allow(dead_code)]
    pub(crate) fn new(range: Range<R>, value: V) -> Self {
        Self { range, value }
    }

    pub fn start_inclusive(&self) -> &R {
        &self.range.start
    }

    /// Not inclusive!
    pub fn end_exclusive(&self) -> &R {
        &self.range.end
    }
}

impl<R> InversionEntry<R, ()>
where
    R: num::Integer + Copy,
{
    /// Internal [`InversionEntry`]`<R, ()>` creation method (for testing).
    ///
    /// ### Panics
    /// This method panics if the provided range is invalid (must not be unbounded on either side or empty).
    #[allow(dead_code)]
    pub(crate) fn new_unit<B>(range: B) -> Self
    where
        B: RangeBounds<R>,
    {
        let range = range_bounds_to_range(range)
            .expect("range should not be unbounded on either side or empty");

        Self { range, value: () }
    }
}

impl<R, V> PartialEq for InversionEntry<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.range.start != other.range.start {
            return false;
        }

        if self.range.end != other.range.end {
            return false;
        }

        self.value == other.value
    }
}


/// An inversion map (i.e. an [inversion list](https://en.wikipedia.org/wiki/Inversion_list)
/// where each range also has an associated value).
///
/// ## Generics
/// Numeric ranges are of type `R` (must implement [`num::Integer`](../num/trait.Integer.html)` + `[`Copy`])
/// and the associated values are of type `V` (must implement [`Clone`]).
pub struct InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    /// A vector of ascending entries (ranges).
    entries: Vec<InversionEntry<R, V>>,
}

impl<R, V> InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    /// Initialize a new empty inversion map.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Initialize a new empty inversion map with the specified
    /// initial `capacity` of its internal vector of entries.
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Returns the first point (smallest value) in this inversion map.
    ///
    /// The returned value is *inclusive*, meaning that semantically,
    /// the value *is* included in the range.
    pub fn start(&self) -> Option<R> {
        self.entries.first().map(|value| *value.start_inclusive())
    }

    /// Returns the last point (largest value) in this inversion map.
    ///
    /// The value is *exclusive*, meaning that semantically,
    /// the value *is not included* in the range.
    pub fn end(&self) -> Option<R> {
        self.entries.last().map(|value| *value.end_exclusive())
    }

    /// Returns the span ([`start`][Self::start] to [`end`][Self::end]) of this inversion map.
    pub fn span(&self) -> Option<Range<R>> {
        let first_start = match self.entries.first() {
            Some(value) => *value.start_inclusive(),
            None => return None,
        };
        let last_end_not_inclusive = match self.entries.last() {
            Some(value) => *value.end_exclusive(),
            None => return None,
        };

        Some(first_start..last_end_not_inclusive)
    }

    /// Returns the amount of entries contained in this inversion map.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns a `bool` indicating whether the inversion map is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Insert a new `range` with the specified `value` into the inversion map.
    ///
    /// The method will return `Err(`[`InsertError`]`)` on error, `Ok(())` otherwise.
    ///
    /// ## Specifics
    /// - If the provided range partially overlaps an existing entry (range), that entry
    /// will be shortened as much as necessary so that the new `range` fits in.
    ///
    /// - If the provided range is inside a single larger range, that range will be split
    /// into two pieces with the new `range` in the middle (the larger range's value will be cloned,
    /// meaning both sides will have the same value).
    ///
    /// - If the provided range completely envelops one or more smaller ranges, those ranges will be
    /// removed from the inversion map and replaced with the given larger `range`.
    pub fn insert<B>(&mut self, range: B, value: V) -> Result<(), InsertError>
    where
        B: RangeBounds<R>,
    {
        let Some(range) = range_bounds_to_range(range) else {
            return Err(InsertError::InvalidRange);
        };

        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);
        let our_entry = InversionEntry { range, value };

        if self.is_empty() {
            self.entries.push(our_entry);
            return Ok(());
        }

        // - Ok indicates the value overlaps an entry (the inner value is the index of the overlapping entry)
        // - Err indicates the value *does not overlap* an entry (the inner value is the index you could
        //   insert that value at for it to still be sorted)
        let start_overlap = self.entry_index_by_value(our_start_inclusive);
        let end_overlap =
            self.entry_index_by_value(our_end_exclusive - R::one());

        match (start_overlap, end_overlap) {
            (
                Ok(start_overlapping_entry_index),
                Ok(end_overlapping_entry_index),
            ) => {
                if start_overlapping_entry_index == end_overlapping_entry_index {
                    let start_overlap_entry_end = *self.entries
                        [start_overlapping_entry_index]
                        .end_exclusive();

                    // If our range goes to either edge of the existing entry, only one new entry will be inserted.
                    // Otherwise, two entries will be created: ours and both subentries that we collided with.
                    if self.entries[start_overlapping_entry_index].range.start
                        == our_start_inclusive
                    {
                        self.entries[start_overlapping_entry_index]
                            .range
                            .start = our_end_exclusive;
                        self.entries
                            .insert(start_overlapping_entry_index, our_entry);
                    } else if self.entries[start_overlapping_entry_index]
                        .range
                        .end
                        == our_end_exclusive
                    {
                        self.entries[start_overlapping_entry_index].range.end =
                            our_start_inclusive;
                        self.entries.insert(
                            start_overlapping_entry_index + 1,
                            our_entry,
                        );
                    } else {
                        // This means our entry splits the overlapping entry into two (we don't reach either edge of it).

                        let right_side_value = self.entries
                            [start_overlapping_entry_index]
                            .value
                            .clone();

                        self.entries[start_overlapping_entry_index].range.end =
                            our_start_inclusive;

                        // The new entry is a subrange of a single larger entry.
                        self.entries.insert(
                            start_overlapping_entry_index + 1,
                            our_entry,
                        );
                        self.entries.insert(
                            start_overlapping_entry_index + 2,
                            InversionEntry {
                                range: our_end_exclusive
                                    ..start_overlap_entry_end,
                                value: right_side_value,
                            },
                        );
                    }
                } else {
                    // The new entry partially overlaps at least one entry on each side,
                    // possibly even fully overlapping some other entry inside its range.

                    self.entries[start_overlapping_entry_index].range.end =
                        our_start_inclusive;
                    self.entries[end_overlapping_entry_index].range.start =
                        our_end_exclusive;

                    self.entries.splice(
                        start_overlapping_entry_index + 1
                            ..end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );
                }
            }
            (Err(start_insert_point), Err(end_insert_point)) => {
                // Doesn't overlap any existing entry - we can simply insert it at the correct point in the vector.

                // Note: if `start_insert_point` and `end_insert_point` don't match, this means the new range
                // encloses one or more other entries. These entries will be removed.

                // TODO Should there be a different method or an option that sets this deletion/overwriting behaviour?
                //      Maybe we could return the removed entries?

                if start_insert_point == end_insert_point {
                    self.entries.insert(start_insert_point, our_entry);
                } else {
                    self.entries.splice(
                        start_insert_point..end_insert_point,
                        std::iter::once(our_entry),
                    );
                }
            }
            (Ok(start_overlapping_entry_index), Err(end_insert_point)) => {
                if self.entries[start_overlapping_entry_index].range.start
                    == our_start_inclusive
                {
                    // Fully overlaps the left entry.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).
                    self.entries.splice(
                        start_overlapping_entry_index..end_insert_point,
                        std::iter::once(our_entry),
                    );
                } else {
                    // Partially overlaps an entry on its left side - we'll shorten the end of that one.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).
                    self.entries[start_overlapping_entry_index].range.end =
                        our_start_inclusive;
                    self.entries.splice(
                        start_overlapping_entry_index + 1..end_insert_point,
                        std::iter::once(our_entry),
                    );
                }
            }
            (Err(start_insert_point), Ok(end_overlapping_entry_index)) => {
                if self.entries[end_overlapping_entry_index].range.end
                    == our_end_exclusive
                {
                    // Fully overlaps the right entry.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).
                    self.entries.splice(
                        start_insert_point..=end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );
                } else {
                    // Partially overlaps an entry on its right side - we'll shorten the start of that one.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).
                    self.entries[end_overlapping_entry_index].range.start =
                        our_end_exclusive;
                    self.entries.splice(
                        start_insert_point..end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );
                }
            }
        };

        Ok(())
    }

    /// Returns the [`InversionEntry`] (i.e. range) that the `value` is inside of, if any.
    pub fn entry_at_value(&self, value: R) -> Option<&InversionEntry<R, V>> {
        let Ok(entry_index) = self.entry_index_by_value(value) else {
            return None;
        };

        self.entries.get(entry_index)
    }

    /// Returns a list of [`InversionEntry`] that exist in the provided `range`.
    #[rustfmt::skip]
    pub fn entries_in_range<B>(
        &self,
        range: B,
    ) -> Result<Vec<&InversionEntry<R, V>>, LookupError>
    where
        B: RangeBounds<R>,
    {
        let Some(range) = range_bounds_to_range(range) else {
            return Err(LookupError::InvalidRange);
        };

        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);

        let start_overlap = self.entry_index_by_value(our_start_inclusive);
        let end_overlap = self.entry_index_by_value(our_end_exclusive - R::one());

        match (start_overlap, end_overlap) {
            (
                Ok(start_overlapping_entry_index),
                Ok(end_overlapping_entry_index),
            ) => {
                Ok(
                    (start_overlapping_entry_index..=end_overlapping_entry_index)
                        .map(|index| &self.entries[index])
                        .collect()
                )
            },
            (Ok(start_overlapping_entry_index), Err(empty_end_point)) => {
                Ok(
                    (start_overlapping_entry_index..empty_end_point)
                        .map(|index| &self.entries[index])
                        .collect()
                )
            },
            (Err(empty_start_point), Ok(end_overlapping_entry_index)) => {
                Ok(
                    (empty_start_point + 1..=end_overlapping_entry_index)
                        .map(|index| &self.entries[index])
                        .collect()
                )
            },
            (Err(empty_start_point), Err(empty_end_point)) => {
                Ok(
                    (empty_start_point + 1..empty_end_point)
                        .map(|index| &self.entries[index])
                        .collect()
                )
            },
        }
    }


    /*
     * Private methods
     */

    fn entry_index_by_value(&self, value: R) -> Result<usize, usize> {
        self.entries.binary_search_by(|entry| {
            let left_ordering = value.cmp(entry.start_inclusive());
            let right_ordering = value.cmp(entry.end_exclusive());

            if left_ordering == Ordering::Less {
                // Smaller than start bound - our target range comes before this entry
                // (i.e. `value˙ > `entry`).
                Ordering::Greater
            } else if left_ordering != Ordering::Less
                && right_ordering == Ordering::Less
            {
                // Inside our bound - larger or equal the start, smaller than the end bound.
                Ordering::Equal
            } else {
                // Larger than (or possibly equal) the end bound - our target range comes after this entry
                // (i.e. `value˙ < `entry`).
                Ordering::Less
            }
        })
    }

    /*
    fn index_and_entry_by_value(
        &self,
        value: V,
    ) -> Result<(usize, &InversionEntry<V>), usize> {
        let entry_index = match self.entry_index_by_value(value) {
            Ok(entry_index) => entry_index,
            Err(potential_insert_point) => {
                return Err(potential_insert_point);
            }
        };

        let entry = &self.entries[entry_index];

        Ok((entry_index, entry))
    }

    fn index_and_entry_mut_by_value(
        &mut self,
        value: V,
    ) -> Result<(usize, &mut InversionEntry<V>), usize> {
        let entry_index = match self.entry_index_by_value(value) {
            Ok(entry_index) => entry_index,
            Err(potential_insert_point) => {
                return Err(potential_insert_point);
            }
        };

        let entry = &mut self.entries[entry_index];

        Ok((entry_index, entry))
    } */
}


impl<R, V> Default for InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}



/*
 * Iterator conversion code.
 * Here we implement iter, iter_mut and an owned iterator
 * as well as `IntoIterator` for &, &mut and owned values,
 * which allows us to use `InversionMap` directly in `for` loops.
 */

impl<R, V> InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    pub fn iter(&self) -> InversionMapIter<R, V> {
        InversionMapIter {
            inner_iterator: self.entries.iter(),
        }
    }

    pub fn iter_mut(&mut self) -> InversionMapMutIter<R, V> {
        InversionMapMutIter {
            inner_iterator: self.entries.iter_mut(),
        }
    }
}

impl<R, V> IntoIterator for InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    type Item = InversionEntry<R, V>;
    type IntoIter = InversionMapIntoIter<R, V>;

    fn into_iter(self) -> InversionMapIntoIter<R, V> {
        InversionMapIntoIter {
            remaining_entries: VecDeque::from(self.entries),
        }
    }
}

impl<'m, R, V> IntoIterator for &'m InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    type Item = &'m InversionEntry<R, V>;
    type IntoIter = InversionMapIter<'m, R, V>;

    fn into_iter(self) -> InversionMapIter<'m, R, V> {
        self.iter()
    }
}

impl<'m, R, V> IntoIterator for &'m mut InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone + PartialEq,
{
    type Item = &'m mut InversionEntry<R, V>;
    type IntoIter = InversionMapMutIter<'m, R, V>;

    fn into_iter(self) -> InversionMapMutIter<'m, R, V> {
        self.iter_mut()
    }
}


#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use super::*;
    use crate::test_utilities::*;

    #[test]
    pub fn continious_inversion_map() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        map.insert(0..=20, ())?;

        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);

        map.insert(0..5, ())?;
        map.insert(5..7, ())?;

        assert!(!map.is_empty());
        assert_eq!(map.len(), 3);

        map.insert(1..3, ())?;

        assert_eq!(map.len(), 5);

        map.insert(14..16, ())?;

        assert_eq!(map.len(), 7);

        map.insert(12..18, ())?;

        assert_eq!(map.len(), 7);

        assert_equal(
            map.into_iter(),
            vec![
                InversionEntry::new_unit(0..1),
                InversionEntry::new_unit(1..3),
                InversionEntry::new_unit(3..5),
                InversionEntry::new_unit(5..7),
                InversionEntry::new_unit(7..12),
                InversionEntry::new_unit(12..18),
                InversionEntry::new_unit(18..=20),
            ],
        );

        Ok(())
    }

    #[test]
    pub fn non_continious_inversion_map() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert(0..10, ())?;
        map.insert(15..18, ())?;

        assert_eq!(map.len(), 2);

        map.insert(18..=19, ())?;

        assert_equal(
            map.iter(),
            vec![
                InversionEntry::new_unit(0..10),
                InversionEntry::new_unit(15..18),
                InversionEntry::new_unit(18..20),
            ]
            .iter(),
        );

        map.insert(0..100, ())?;

        assert_equal(
            map.into_iter(),
            vec![InversionEntry::new_unit(0..100)],
        );

        Ok(())
    }

    #[test]
    pub fn entry_at_value() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert(0..10, ())?;
        map.insert(10..14, ())?;
        map.insert(2..6, ())?;
        map.insert(20..30, ())?;

        assert_eq!(
            map.entry_at_value(2),
            Some(&InversionEntry::new_unit(2..6))
        );
        assert_eq!(
            map.entry_at_value(5),
            Some(&InversionEntry::new_unit(2..6))
        );
        assert_eq!(
            map.entry_at_value(6),
            Some(&InversionEntry::new_unit(6..10))
        );

        assert_eq!(
            map.entry_at_value(21),
            Some(&InversionEntry::new_unit(20..30))
        );

        Ok(())
    }

    #[test]
    pub fn entries_in_range() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert(0..10, ())?;
        map.insert(10..14, ())?;
        map.insert(2..6, ())?;
        map.insert(20..30, ())?;

        assert_eq!(
            map.entries_in_range(3..8),
            Ok(vec![
                &InversionEntry::new_unit(2..6),
                &InversionEntry::new_unit(6..10),
            ])
        );

        assert_eq!(
            map.entries_in_range(0..2),
            Ok(vec![&InversionEntry::new_unit(0..2)])
        );

        assert_eq!(
            map.entries_in_range(10..14),
            Ok(vec![&InversionEntry::new_unit(10..14)])
        );

        assert_eq!(
            map.entries_in_range(10..28),
            Ok(vec![
                &InversionEntry::new_unit(10..14),
                &InversionEntry::new_unit(20..30),
            ])
        );


        Ok(())
    }
}
