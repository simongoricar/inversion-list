use std::ops::{Range, RangeBounds};

use crate::{
    error::{InsertError, LookupError},
    InversionMap,
};

pub struct InversionList<RangeIndex>
where
    RangeIndex: num::Integer + Copy,
{
    inner: InversionMap<RangeIndex, ()>,
}

impl<R> InversionList<R>
where
    R: num::Integer + Copy,
{
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            inner: InversionMap::new(),
        }
    }

    pub fn new_with_capacity(capacity: usize) -> Self {
        Self {
            inner: InversionMap::new_with_capacity(capacity),
        }
    }

    pub fn start(&self) -> Option<R> {
        self.inner.start()
    }

    pub fn end(&self) -> Option<R> {
        self.inner.end()
    }

    pub fn span(&self) -> Option<Range<R>> {
        self.inner.span()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn insert_with_overwrite<B>(
        &mut self,
        range: B,
    ) -> Result<Vec<Range<R>>, InsertError>
    where
        B: RangeBounds<R>,
    {
        Ok(self
            .inner
            .insert_with_overwrite(range, ())?
            .into_iter()
            .map(|entry| entry.range)
            .collect())
    }

    pub fn try_insert<B>(&mut self, range: B) -> Result<(), InsertError>
    where
        B: RangeBounds<R>,
    {
        self.inner.try_insert(range, ())
    }

    pub fn entry_at_position(&self, position: R) -> Option<&Range<R>> {
        self.inner
            .entry_at_position(position)
            .map(|entry| &entry.range)
    }

    pub fn entries_in_range<B>(
        &self,
        range: B,
    ) -> Result<Vec<&Range<R>>, LookupError>
    where
        B: RangeBounds<R>,
    {
        self.inner.entries_in_range(range).map(|entry_vec| {
            entry_vec.into_iter().map(|entry| &entry.range).collect()
        })
    }
}
