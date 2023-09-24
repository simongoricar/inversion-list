use std::collections::VecDeque;

use crate::InversionEntry;

/// An iterator over a borrowed [`InversionMap`][crate::InversionMap].
///
/// To create this iterator, see the [`InversionMap::iter`][crate::InversionMap::iter] method.
/// Produces borrowed [`InversionEntry`][InversionEntry] elements.
pub struct InversionMapIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    pub(crate) inner_iterator: std::slice::Iter<'m, InversionEntry<R, V>>,
}

impl<'m, R, V> Iterator for InversionMapIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    type Item = &'m InversionEntry<R, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_iterator.size_hint()
    }
}

impl<'m, R, V> ExactSizeIterator for InversionMapIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    fn len(&self) -> usize {
        self.inner_iterator.len()
    }
}


/// An iterator over a mutably borrowed [`InversionMap`][crate::InversionMap].
///
/// To create this iterator, see the [`InversionMap::iter_mut`][crate::InversionMap::iter_mut] method.
/// Produces mutably borrowed [`InversionEntry`][InversionEntry] elements.
pub struct InversionMapMutIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    pub(crate) inner_iterator: std::slice::IterMut<'m, InversionEntry<R, V>>,
}

impl<'m, R, V> Iterator for InversionMapMutIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    type Item = &'m mut InversionEntry<R, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iterator.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner_iterator.size_hint()
    }
}

impl<'m, R, V> ExactSizeIterator for InversionMapMutIter<'m, R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    fn len(&self) -> usize {
        self.inner_iterator.len()
    }
}



/// An iterator over an owned [`InversionMap`][crate::InversionMap].
///
/// To create this iterator, see the [`InversionMap::into_iter`][crate::InversionMap::into_iter] method.
/// Produces owned [`InversionEntry`][InversionEntry] elements.
pub struct InversionMapIntoIter<R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    pub(crate) remaining_entries: VecDeque<InversionEntry<R, V>>,
}

impl<R, V> Iterator for InversionMapIntoIter<R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    type Item = InversionEntry<R, V>;

    fn next(&mut self) -> Option<Self::Item> {
        self.remaining_entries.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining_length = self.remaining_entries.len();

        (remaining_length, Some(remaining_length))
    }
}

impl<R, V> ExactSizeIterator for InversionMapIntoIter<R, V>
where
    R: num::Integer + Copy,
    V: Clone,
{
    fn len(&self) -> usize {
        self.remaining_entries.len()
    }
}
