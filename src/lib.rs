//! An [inversion list](https://en.wikipedia.org/wiki/Inversion_list) implementation.
//!
//! ## What is an inversion list (and map)
//! An **inversion list** is a data structure that describes an ascending list of non-overlapping integer ranges.
//!
//! For example, `0..10`, `10..12` and `12..15` is a continious inversion list.
//! The list can also be non-continious, for example: `0..5`, `20..21`, `25..30`.
//!
//! An **inversion map** is an extension of the inversion list structure where each range has an associated value
//! (for example, `0..10 (true)`, `10..12 (false)` and `12..15 (true)`).
//!
//! ## Examples
//! You may call [`InversionMap::new`] to create an empty inversion map, then use [`InversionMap::insert`]
//! to add new ranges.
//!
//! ```rust
//! # use inversion_list::InversionMap;
//!
//! let mut inversion_map: InversionMap<u8, bool> = InversionMap::new();
//!
//! inversion_map
//!     .insert(0..5, false)
//!     .expect("Failed to insert first value into inversion map.");
//!
//! inversion_map
//!     .insert(5..10, true)
//!     .expect("Failed to insert second value into inversion map.");
//!
//! inversion_map
//!     .insert(15..18, true)
//!     .expect("Failed to insert second value into inversion map.");
//!
//! assert_eq!(inversion_map.len(), 3);
//! assert_eq!(inversion_map.span(), Some(0..18));
//! ```
//!
//! ---
//!
//! #### Attribution
//!
//! Heavily inspired and partially adapted from
//! [`Veykril/inversion-list`](https://github.com/Veykril/inversion-list),
//! which is licensed under MIT.
//!
//! <details>
//! <summary>
//!
//! `Veykril/inversion-list`'s license</summary>
//!
//! ```markdown
//! MIT License
//!
//! Copyright (c) 2020-2022 Lukas Wirth <Veykril>
//!
//! Permission is hereby granted, free of charge, to any person obtaining a copy
//! of this software and associated documentation files (the "Software"), to deal
//! in the Software without restriction, including without limitation the rights
//! to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//! copies of the Software, and to permit persons to whom the Software is
//! furnished to do so, subject to the following conditions:
//!
//! The above copyright notice and this permission notice shall be included in all
//! copies or substantial portions of the Software.
//!
//! THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//! IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//! FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//! AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//! LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//! OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//! SOFTWARE.
//! ```
//! </details>

pub mod error;
pub mod iter;
mod map;
mod utilities;

#[cfg(test)]
pub mod test_utilities;

pub use map::{InversionEntry, InversionMap};
