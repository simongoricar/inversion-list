use std::{
    cmp::Ordering,
    collections::VecDeque,
    mem::swap,
    ops::{Range, RangeBounds},
};

use crate::{
    error::{InsertError, LookupError},
    iter::{InversionMapIntoIter, InversionMapIter, InversionMapMutIter},
    utilities::range_bounds_to_range,
};

/// A single inversion list map ([`InversionMap`]) entry.
///
/// Numeric range is of type `R` (must implement [`num::Integer`](../num/trait.Integer.html)` + `[`Copy`])
/// and the associated value is of type `V` (must implement [`Clone`]).
#[derive(Debug)]
pub struct InversionEntry<R, V>
where
    R: num::Integer + Copy,
{
    pub(crate) range: Range<R>,
    pub value: V,
}

impl<R, V> InversionEntry<R, V>
where
    R: num::Integer + Copy,
{
    /// A half-open range describing the inversion list entry range.
    pub fn range(&self) -> &Range<R> {
        &self.range
    }

    /// The start value of the inversion list entry (*inclusive end of the range*).
    pub fn start(&self) -> &R {
        &self.range.start
    }

    /// The end value of the inversion list entry (*exclusive end of the range!*).
    pub fn end(&self) -> &R {
        &self.range.end
    }
}

impl<R, V> Clone for InversionEntry<R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            range: self.range.clone(),
            value: self.value.clone(),
        }
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
/// where each range also has an associated value, akin to a sorted `HashMap` where the keys are ranges).
///
/// ## Generics
/// Numeric type used when specifying the ranges can be set using the `RangeType` generic
/// (type must implement [`num::Integer`](../num/trait.Integer.html)` + `[`Copy`]).
///
/// The type of the associated range value is specified using the `Value` generic
/// (type must implement [`Clone`]).
pub struct InversionMap<RangeType, Value>
where
    RangeType: num::Integer + Copy,
{
    /// A vector containing *ascending* entries (ranges and values)
    /// of the inversion map.
    entries: Vec<InversionEntry<RangeType, Value>>,
}

impl<R, V> InversionMap<R, V>
where
    R: num::Integer + Copy,
{
    /// Create an empty inversion map.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Create an empty inversion map with the specified
    /// initial `capacity` of its internal entries [`Vec`].
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self {
            entries: Vec::with_capacity(capacity),
        }
    }

    /// Returns the start of the range of the entire inversion map.
    /// This is the same as taking the start of the range of the smallest (i.e. first) inversion list entry.
    ///
    /// The value represents the *inclusive* part of the half-open range.
    /// This means that *the start value is included in the range*.
    pub fn start(&self) -> Option<R> {
        self.entries.first().map(|value| *value.start())
    }

    /// Returns the end of the range of the entire inversion map.
    /// This is the same as taking the end of the range of the largest (i.e. last) inversion list entry.
    ///
    /// The value represents and *exclusive* part of the half-open range.
    /// This means that *the end value is not included in the range*.
    pub fn end(&self) -> Option<R> {
        self.entries.last().map(|value| *value.end())
    }

    /// Returns the full range — also called a *span* — of this inversion map.
    ///
    /// This is the same as taking the start of the range of the smallest (i.e. first) entry
    /// and the end of the range of the largest (i.e. last) entry.
    ///
    /// This is also the same as constructing a half-open range using the values from
    /// [`self.start()`][Self::start] to [`self.end()`][Self::end].
    pub fn span(&self) -> Option<Range<R>> {
        let first_start = match self.entries.first() {
            Some(value) => *value.start(),
            None => return None,
        };
        let last_end_not_inclusive = match self.entries.last() {
            Some(value) => *value.end(),
            None => return None,
        };

        Some(first_start..last_end_not_inclusive)
    }

    /// Returns the number of entries contained in this inversion map.
    ///
    /// This is not the same as a [`self.span()`][Self::span].
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns a `bool` indicating whether the inversion map is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Attempt to insert a new `range` with the specified `value` into the inversion map.
    ///
    /// Unlike [`Self::insert_with_overwrite`], **this operation does not modify or delete existing entries**.
    /// It returns `Err(`[`InsertError::CollidesWithExistingEntry`]`)` if the insert would have collided
    /// with an existing inversion map entry.
    pub fn try_insert<B>(
        &mut self,
        range: B,
        value: V,
    ) -> Result<(), InsertError>
    where
        B: RangeBounds<R>,
    {
        // This converts any possible kind of range bound into the `start..end` range,
        // where `start` is inclusive and `end` is exclusive.
        // If the range is unbounded or only bounded at one side, this will immediately return an error.
        let Some(range) = range_bounds_to_range(range) else {
            return Err(InsertError::InvalidRange);
        };


        // - `Ok` indicates the value overlaps an existing entry
        //   (the inner value is the index of the overlapping entry)
        // - `Err` indicates the value *does not overlap* an entry
        //   (the inner value is the index you could insert that value at for it to still be sorted)
        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);
        let our_entry = InversionEntry { range, value };

        let start_overlap = self.entry_index_by_position(our_start_inclusive);
        let end_overlap =
            self.entry_index_by_position(our_end_exclusive - R::one());


        if let Err(start_insert_point) = start_overlap {
            if let Err(end_insert_point) = end_overlap {
                if start_insert_point == end_insert_point {
                    // The new entry does not overlap any existing entry.
                    // As such we can simply insert it at the correct point in the vector and we're done.
                    self.entries.insert(start_insert_point, our_entry);

                    return Ok(());
                }
            }
        }

        Err(InsertError::CollidesWithExistingEntry)
    }

    /// Returns a reference to the [`InversionEntry`] (i.e. range-value pair)
    /// that exists at the provided `position`, if any.
    pub fn entry_at_position(
        &self,
        position: R,
    ) -> Option<&InversionEntry<R, V>> {
        let Ok(entry_index) = self.entry_index_by_position(position) else {
            return None;
        };

        self.entries.get(entry_index)
    }

    /// Returns a mutable reference to the [`InversionEntry`] (i.e. range-value pair)
    /// that exists at the provided `position`, if any.
    ///
    /// In general, this is useful only if you wish to modify the value stored in some entry.
    pub fn entry_at_position_mut(
        &mut self,
        position: R,
    ) -> Option<&mut InversionEntry<R, V>> {
        let Ok(entry_index) = self.entry_index_by_position(position) else {
            return None;
        };

        self.entries.get_mut(entry_index)
    }

    /// Returns a list of references to [`InversionEntry`] that exist — partially or fully — inside the provided `range`.
    ///
    /// The returned vector can be empty (i.e. no results does not equal an error).
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

        let start_overlap = self.entry_index_by_position(our_start_inclusive);
        let end_overlap = self.entry_index_by_position(our_end_exclusive - R::one());

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

    /// Returns a list of mutable references to [`InversionEntry`] that exist — partially or fully — inside the provided `range`.
    ///
    /// The returned vector can be empty (i.e. no results does not equal an error).
    ///
    /// In general, this is useful only if you wish to modify the value stored in some entry.
    pub fn entries_in_range_mut<B>(
        &mut self,
        range: B,
    ) -> Result<&mut [InversionEntry<R, V>], LookupError>
    where
        B: RangeBounds<R>,
    {
        let Some(range) = range_bounds_to_range(range) else {
            return Err(LookupError::InvalidRange);
        };

        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);

        let start_overlap = self.entry_index_by_position(our_start_inclusive);
        let end_overlap =
            self.entry_index_by_position(our_end_exclusive - R::one());

        match (start_overlap, end_overlap) {
            (
                Ok(start_overlapping_entry_index),
                Ok(end_overlapping_entry_index),
            ) => {
                let (mutable_slice, _) =
                    self.entries.split_at_mut(end_overlapping_entry_index + 1);
                let (_, mutable_slice) =
                    mutable_slice.split_at_mut(start_overlapping_entry_index);

                Ok(mutable_slice)
            }
            (Ok(start_overlapping_entry_index), Err(empty_end_point)) => {
                let (mutable_slice, _) =
                    self.entries.split_at_mut(empty_end_point);
                let (_, mutable_slice) =
                    mutable_slice.split_at_mut(start_overlapping_entry_index);

                Ok(mutable_slice)
            }
            (Err(empty_start_point), Ok(end_overlapping_entry_index)) => {
                let (mutable_slice, _) =
                    self.entries.split_at_mut(end_overlapping_entry_index + 1);
                let (_, mutable_slice) =
                    mutable_slice.split_at_mut(empty_start_point + 1);

                Ok(mutable_slice)
            }
            (Err(empty_start_point), Err(empty_end_point)) => {
                let (mutable_slice, _) =
                    self.entries.split_at_mut(empty_end_point);
                let (_, mutable_slice) =
                    mutable_slice.split_at_mut(empty_start_point + 1);

                Ok(mutable_slice)
            }
        }
    }


    /*
     * Private methods
     */



    /// Find an inversion map entry that exists at the specified `position`.
    ///
    /// # Return value
    /// From the standard library ([`binary_search`][Vec::binary_search_by]):
    /// If the value is found then [`Result::Ok`] is returned, containing the index of the matching element. [...]
    /// If the value is not found then [`Result::Err`] is returned, containing the index where a matching element
    /// could be inserted while maintaining sorted order.
    fn entry_index_by_position(&self, position: R) -> Result<usize, usize> {
        self.entries.binary_search_by(|entry| {
            let left_ordering = position.cmp(entry.start());
            let right_ordering = position.cmp(entry.end());

            if left_ordering == Ordering::Less {
                // Smaller than start bound: our target range comes before this entry
                // (i.e. `value˙ > `entry`).
                Ordering::Greater
            } else if left_ordering != Ordering::Less
                && right_ordering == Ordering::Less
            {
                // Inside our bound: larger or equal the start, smaller than the end bound.
                Ordering::Equal
            } else {
                // Larger than (or possibly equal to) the end bound - our target range comes after this entry
                // (i.e. `value˙ < `entry`).
                Ordering::Less
            }
        })
    }
}

/// An [`InversionMap`] impl block containing the implementation for [`Self::insert_with_overwrite`],
/// which makes sense only if type of `Value` is cloneable (otherwise it would be impossible to split ranges).
impl<R, V> InversionMap<R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    /// Insert a new `range` with the specified `value` into the inversion map.
    ///
    /// **This operation might modify or delete existing entries** (see details below).
    /// Deleted entries are returned inside the `Ok` result variant.
    ///
    /// # Insertion details
    /// - If the provided `range` partially overlaps an existing entry or entries on either or both sides,
    /// the overlapping entries will be shortened as much as necessary so that the new `range` fits in.
    ///
    /// - If the provided `range` is inside of a single larger existing range, the larger range will be split
    /// into two pieces with the new `range` in the middle.
    ///   The associated value of the larger range will be cloned, meaning both sides will still contain the same value.
    ///
    /// - If the provided `range` completely envelops one or more smaller existing ranges, those enveloped ranges *will be
    /// removed from the inversion map* and replaced with the new larger `range`.
    pub fn insert_with_overwrite<B>(
        &mut self,
        range: B,
        value: V,
    ) -> Result<Vec<InversionEntry<R, V>>, InsertError>
    where
        B: RangeBounds<R>,
    {
        // This converts any possible kind of range bound into the `start..end` range,
        // where `start` is inclusive and `end` is exclusive.
        // If the range is unbounded or only bounded at one side, this will immediately return an error.
        let Some(range) = range_bounds_to_range(range) else {
            return Err(InsertError::InvalidRange);
        };


        // - `Ok` indicates the value overlaps an existing entry
        //   (the inner value is the index of the overlapping entry)
        // - `Err` indicates the value *does not overlap* an entry
        //   (the inner value is the index you could insert that value at for it to still be sorted)
        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);

        let start_overlap = self.entry_index_by_position(our_start_inclusive);
        let end_overlap =
            self.entry_index_by_position(our_end_exclusive - R::one());


        Ok(self.perform_insert(range, value, start_overlap, end_overlap))
    }

    fn perform_insert(
        &mut self,
        range: Range<R>,
        value: V,
        start_overlap: Result<usize, usize>,
        end_overlap: Result<usize, usize>,
    ) -> Vec<InversionEntry<R, V>> {
        let (our_start_inclusive, our_end_exclusive) = (range.start, range.end);
        let our_entry = InversionEntry { range, value };

        // If our list doesn't have any entries yet, we don't need to check for any collisions.
        if self.is_empty() {
            self.entries.push(our_entry);
            return Vec::with_capacity(0);
        }

        match (start_overlap, end_overlap) {
            (
                Ok(start_overlapping_entry_index),
                Ok(end_overlapping_entry_index),
            ) => {
                // The new entry collides with existing entry or entries.
                // More precisely, the new entry collides with all entries between
                // `start_overlapping_entry_index..=end_overlapping_entry_index`.

                if start_overlapping_entry_index == end_overlapping_entry_index {
                    let start_overlap_entry_end =
                        *self.entries[start_overlapping_entry_index].end();

                    if self.entries[start_overlapping_entry_index].range.start
                        == our_start_inclusive
                        && self.entries[start_overlapping_entry_index].range.end
                            == our_end_exclusive
                    {
                        let mut our_entry = our_entry;

                        // The new entry fully matches an existing entry, we'll replace.
                        swap(
                            &mut our_entry,
                            &mut self.entries[start_overlapping_entry_index],
                        );

                        // This is the replaced entry, see `swap` above.
                        vec![our_entry]
                    } else if self.entries[start_overlapping_entry_index]
                        .range
                        .start
                        == our_start_inclusive
                    {
                        // Our range goes to one edge of the existing entry, only one new entry will be inserted.
                        self.entries[start_overlapping_entry_index]
                            .range
                            .start = our_end_exclusive;
                        self.entries
                            .insert(start_overlapping_entry_index, our_entry);

                        Vec::with_capacity(0)
                    } else if self.entries[start_overlapping_entry_index]
                        .range
                        .end
                        == our_end_exclusive
                    {
                        // Our range goes to one edge of the existing entry, only one new entry will be inserted.
                        self.entries[start_overlapping_entry_index].range.end =
                            our_start_inclusive;
                        self.entries.insert(
                            start_overlapping_entry_index + 1,
                            our_entry,
                        );

                        Vec::with_capacity(0)
                    } else {
                        // This means our entry splits the overlapping entry into two (we don't reach either edge of it).
                        // Two entries will be created: ours and both subentries that we collided with.

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

                        Vec::with_capacity(0)
                    }
                } else {
                    // The new entry partially overlaps at least one entry on each side,
                    // possibly even fully overlapping some other entry inside its range.

                    self.entries[start_overlapping_entry_index].range.end =
                        our_start_inclusive;
                    self.entries[end_overlapping_entry_index].range.start =
                        our_end_exclusive;

                    let removed_entries = self.entries.splice(
                        start_overlapping_entry_index + 1
                            ..end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );

                    removed_entries.collect()
                }
            }
            (Err(start_insert_point), Err(end_insert_point)) => {
                if start_insert_point == end_insert_point {
                    // The new entry does not overlap any existing entry.
                    // As such we can simply insert it at the correct point in the vector and we're done.

                    self.entries.insert(start_insert_point, our_entry);
                    Vec::with_capacity(0)
                } else {
                    // The new entry completely envelops existing entries on indexes `start_insert_point..end_insert_point`.
                    // Those items will be replaced with the new entry with the enveloping range.

                    let removed_entries = self.entries.splice(
                        start_insert_point..end_insert_point,
                        std::iter::once(our_entry),
                    );
                    removed_entries.collect()
                }
            }
            (Ok(start_overlapping_entry_index), Err(end_insert_point)) => {
                if self.entries[start_overlapping_entry_index].range.start
                    == our_start_inclusive
                {
                    // The new entry collides on its left (smaller) side: it fully overlaps that entry.
                    // Can also completely envelop one or more existing entries inside its range (those will be removed).

                    let removed_entries = self.entries.splice(
                        start_overlapping_entry_index..end_insert_point,
                        std::iter::once(our_entry),
                    );
                    removed_entries.collect()
                } else {
                    // The new entry collides on its left (smaller) side: it partially overlaps that
                    // entry - we'll shorten the end of that one.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).

                    self.entries[start_overlapping_entry_index].range.end =
                        our_start_inclusive;
                    let removed_entries = self.entries.splice(
                        start_overlapping_entry_index + 1..end_insert_point,
                        std::iter::once(our_entry),
                    );
                    removed_entries.collect()
                }
            }
            (Err(start_insert_point), Ok(end_overlapping_entry_index)) => {
                if self.entries[end_overlapping_entry_index].range.end
                    == our_end_exclusive
                {
                    // The new entry collides on its right (larger) side: it fully overlaps that entry.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).

                    let removed_entries = self.entries.splice(
                        start_insert_point..=end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );
                    removed_entries.collect()
                } else {
                    // The new entry collides on its right (larger) side: it partially overlaps that
                    // entry - we'll shorten the start of that one.
                    // Can also completely envelop one or more existing entry inside its range (those will be removed).

                    self.entries[end_overlapping_entry_index].range.start =
                        our_end_exclusive;
                    let removed_entries = self.entries.splice(
                        start_insert_point..end_overlapping_entry_index,
                        std::iter::once(our_entry),
                    );
                    removed_entries.collect()
                }
            }
        }
    }
}


impl<R, V> Default for InversionMap<R, V>
where
    R: num::Integer + Copy,
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
    fn entry_ok() {
        let entry = InversionEntry {
            range: 5..10,
            value: -12,
        };

        let second_entry = InversionEntry {
            range: 5..10,
            value: -11,
        };

        let third_entry = InversionEntry {
            range: 5..10,
            value: -12,
        };

        assert_eq!(entry.start(), &5);
        assert_eq!(entry.end(), &10);
        assert_eq!(entry.range(), &(5..10));
        assert_eq!(entry.value, -12);

        assert_ne!(entry, second_entry);
        assert_eq!(entry, third_entry);
    }

    #[test]
    fn continious_inversion_map() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        map.insert_with_overwrite(0..=20, ())?;

        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);

        map.insert_with_overwrite(0..5, ())?;
        map.insert_with_overwrite(5..7, ())?;

        assert!(!map.is_empty());
        assert_eq!(map.len(), 3);

        map.insert_with_overwrite(1..3, ())?;

        assert_eq!(map.len(), 5);

        map.insert_with_overwrite(14..16, ())?;

        assert_eq!(map.len(), 7);

        map.insert_with_overwrite(12..18, ())?;

        assert_eq!(map.len(), 7);

        assert_equal(
            map,
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
    fn non_continious_inversion_map() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert_with_overwrite(0..10, ())?;
        map.insert_with_overwrite(15..18, ())?;

        assert_eq!(map.len(), 2);

        map.insert_with_overwrite(18..=19, ())?;

        assert_equal(
            map.iter(),
            [
                InversionEntry::new_unit(0..10),
                InversionEntry::new_unit(15..18),
                InversionEntry::new_unit(18..20),
            ]
            .iter(),
        );

        map.insert_with_overwrite(0..100, ())?;

        assert_equal(map, vec![InversionEntry::new_unit(0..100)]);

        Ok(())
    }

    #[test]
    fn entry_at_value() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert_with_overwrite(0..10, ())?;
        map.insert_with_overwrite(10..14, ())?;
        map.insert_with_overwrite(2..6, ())?;
        map.insert_with_overwrite(20..30, ())?;

        assert_eq!(
            map.entry_at_position(2),
            Some(&InversionEntry::new_unit(2..6))
        );
        assert_eq!(
            map.entry_at_position(5),
            Some(&InversionEntry::new_unit(2..6))
        );
        assert_eq!(
            map.entry_at_position(6),
            Some(&InversionEntry::new_unit(6..10))
        );

        assert_eq!(
            map.entry_at_position(21),
            Some(&InversionEntry::new_unit(20..30))
        );

        Ok(())
    }

    #[test]
    fn entries_in_range() -> TestResult {
        let mut map = InversionMap::<u8, ()>::new();

        map.insert_with_overwrite(0..10, ())?;
        map.insert_with_overwrite(10..14, ())?;
        map.insert_with_overwrite(2..6, ())?;
        map.insert_with_overwrite(20..30, ())?;

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

    #[test]
    fn try_insert() {
        let mut map = InversionMap::<u8, ()>::new();

        map.try_insert(0..2, ()).unwrap();
        map.try_insert(2..10, ()).unwrap();
        map.try_insert(12..14, ()).unwrap();

        assert_eq!(
            map.try_insert(2..4, ()),
            Err(InsertError::CollidesWithExistingEntry)
        );

        assert_eq!(
            map.try_insert(10..13, ()),
            Err(InsertError::CollidesWithExistingEntry)
        );
    }

    #[test]
    fn insert_with_replace() {
        let mut map = InversionMap::<u8, ()>::new();

        map.try_insert(4..12, ()).unwrap();

        assert_eq!(
            map.insert_with_overwrite(4..12, ()),
            Ok(vec![InversionEntry::new_unit(4..12)])
        );

        assert_eq!(
            map.insert_with_overwrite(3..13, ()),
            Ok(vec![InversionEntry::new_unit(4..12)])
        );
    }
}
