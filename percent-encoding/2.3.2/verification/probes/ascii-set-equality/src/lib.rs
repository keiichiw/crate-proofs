#![no_std]

#[path = "../../../../crate/src/ascii_set.rs"]
mod ascii_set;

#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
#[ensures(result == (left.deep_model() == right.deep_model()))]
pub fn check_ascii_set_equality(left: &ascii_set::AsciiSet, right: &ascii_set::AsciiSet) -> bool {
    left == right
}
