// Copyright 2013-2016 The rust-url developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::{fmt, mem, ops};
#[cfg(creusot)]
use creusot_std::prelude::*;

/// Represents a set of characters or bytes in the ASCII range.
///
/// This is used in [`percent_encode`] and [`utf8_percent_encode`].
/// This is similar to [percent-encode sets](https://url.spec.whatwg.org/#percent-encoded-bytes).
///
/// Use the `add` method of an existing set to define a new set. For example:
///
/// [`percent_encode`]: crate::percent_encode
/// [`utf8_percent_encode`]: crate::utf8_percent_encode
///
/// ```
/// use percent_encoding::{AsciiSet, CONTROLS};
///
/// /// https://url.spec.whatwg.org/#fragment-percent-encode-set
/// const FRAGMENT: &AsciiSet = &CONTROLS.add(b' ').add(b'"').add(b'<').add(b'>').add(b'`');
/// ```
pub struct AsciiSet {
    mask: [Chunk; ASCII_RANGE_LEN / BITS_PER_CHUNK],
}

impl fmt::Debug for AsciiSet {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let struct_name = "AsciiSet";
        let field_name = "mask";
        #[cfg(creusot)]
        let mut trace = crate::debug_trace::DebugTrace::empty(struct_name);
        let mut builder = crate::debug_trace::start(
            formatter,
            struct_name,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        crate::debug_trace::field_words(
            &mut builder,
            field_name,
            &self.mask,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        let result = crate::debug_trace::finish(
            &mut builder,
            #[cfg(creusot)]
            trace.borrow_mut(),
        );
        #[cfg(creusot)]
        {
            proof_assert!(trace.struct_name == struct_name);
            proof_assert!(trace.field_names.len() == 1);
            proof_assert!(trace.field_names[0] == field_name);
            proof_assert!(trace.field_type_tags.len() == 1);
            proof_assert!(trace.field_type_tags[0] == 0u8);
            proof_assert!(trace.word_values.len() == 1);
            proof_assert!(*trace.word_values[0] == self.mask@);
            proof_assert!(trace.byte_values.len() == 0);
            proof_assert!(trace.iter_values.len() == 0);
            proof_assert!(trace.ascii_set_values.len() == 0);
            proof_assert!(
                trace.finish_status
                    == Some(match result {
                        Ok(()) => true,
                        Err(_) => false,
                    })
            );
        }
        result
    }
}

#[cfg(creusot)]
impl DeepModel for AsciiSet {
    type DeepModelTy = Seq<u32>;

    #[logic(open(self))]
    #[cfg_attr(creusot, ensures(result == self.mask_words()))]
    fn deep_model(self) -> Seq<u32> {
        self.mask_words()
    }
}

impl PartialEq for AsciiSet {
    #[cfg_attr(creusot, ensures(result == (self.deep_model() == other.deep_model())))]
    fn eq(&self, other: &Self) -> bool {
        self.mask[0] == other.mask[0]
            && self.mask[1] == other.mask[1]
            && self.mask[2] == other.mask[2]
            && self.mask[3] == other.mask[3]
    }
}

impl Eq for AsciiSet {}

type Chunk = u32;

const ASCII_RANGE_LEN: usize = 0x80;

const BITS_PER_CHUNK: usize = 8 * mem::size_of::<Chunk>();

impl AsciiSet {
    /// Logical view of the four mask words used to represent this set.
    #[cfg(creusot)]
    #[logic]
    #[ensures(result.len() == 4)]
    pub fn mask_words(&self) -> Seq<u32> {
        pearlite! { Seq::create(4, |i: Int| self.mask@[i]) }
    }

    /// An empty set.
    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(AsciiSet::EMPTY.mask_words().len() == 4))]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> AsciiSet::EMPTY.mask_words()[i] == 0u32 }))]
    pub const EMPTY: Self = Self {
        mask: [0; ASCII_RANGE_LEN / BITS_PER_CHUNK],
    };

    /// Called with UTF-8 bytes rather than code points.
    /// Not used for non-ASCII bytes.
    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, requires(byte@ < 128))]
    #[cfg_attr(creusot, ensures(result == contains_model(self, byte)))]
    pub(crate) const fn contains(&self, byte: u8) -> bool {
        let chunk = self.mask[byte as usize / BITS_PER_CHUNK];
        let mask = 1 << (byte as usize % BITS_PER_CHUNK);
        (chunk & mask) != 0
    }

    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(result == (byte@ >= 128 || contains_model(self, byte))))]
    #[cfg_attr(creusot, ensures(result == crate::encode_models::should_encode_model(self.mask_words(), byte)))]
    pub(crate) fn should_percent_encode(&self, byte: u8) -> bool {
        byte >= 128 || self.contains(byte)
    }

    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, requires(byte@ < 128))]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == if i == byte@ / 32 { self.mask_words()[i] | (1u32 << (byte & 31u8)) } else { self.mask_words()[i] } }))]
    pub const fn add(&self, byte: u8) -> Self {
        let mut mask = self.mask;
        mask[byte as usize / BITS_PER_CHUNK] |= 1 << (byte as usize % BITS_PER_CHUNK);
        Self { mask }
    }

    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, requires(byte@ < 128))]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == if i == byte@ / 32 { self.mask_words()[i] & !(1u32 << (byte & 31u8)) } else { self.mask_words()[i] } }))]
    pub const fn remove(&self, byte: u8) -> Self {
        let mut mask = self.mask;
        mask[byte as usize / BITS_PER_CHUNK] &= !(1 << (byte as usize % BITS_PER_CHUNK));
        Self { mask }
    }

    /// Return the union of two sets.
    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == self.mask_words()[i] | other.mask_words()[i] }))]
    pub const fn union(&self, other: Self) -> Self {
        let mask = [
            self.mask[0] | other.mask[0],
            self.mask[1] | other.mask[1],
            self.mask[2] | other.mask[2],
            self.mask[3] | other.mask[3],
        ];
        Self { mask }
    }

    /// Return the negation of the set.
    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == !self.mask_words()[i] }))]
    pub const fn complement(&self) -> Self {
        let mask = [!self.mask[0], !self.mask[1], !self.mask[2], !self.mask[3]];
        Self { mask }
    }
}

#[cfg(creusot)]
#[logic(open)]
#[bitwise_proof]
pub(crate) fn contains_model(set: &AsciiSet, byte: u8) -> bool {
    pearlite! { byte@ < 128 && set.mask_words()[byte@ / 32] & (1u32 << (byte & 31u8)) != 0u32 }
}

impl ops::Add for AsciiSet {
    type Output = Self;

    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == self.mask_words()[i] | other.mask_words()[i] }))]
    fn add(self, other: Self) -> Self {
        self.union(other)
    }
}

impl ops::Not for AsciiSet {
    type Output = Self;

    #[cfg_attr(creusot, bitwise_proof)]
    #[cfg_attr(creusot, ensures(pearlite! { forall<i: Int> 0 <= i && i < 4 ==> result.mask_words()[i] == !self.mask_words()[i] }))]
    fn not(self) -> Self {
        self.complement()
    }
}

/// The set of 0x00 to 0x1F (C0 controls), and 0x7F (DEL).
///
/// Note that this includes the newline and tab characters, but not the space 0x20.
///
/// <https://url.spec.whatwg.org/#c0-control-percent-encode-set>
#[cfg_attr(creusot, ensures(CONTROLS.mask_words().len() == 4))]
#[cfg_attr(creusot, ensures(CONTROLS.mask_words()[0] == 0xffffffffu32 && CONTROLS.mask_words()[1] == 0u32 && CONTROLS.mask_words()[2] == 0u32 && CONTROLS.mask_words()[3] == 0x80000000u32))]
#[cfg_attr(creusot, bitwise_proof)]
pub const CONTROLS: &AsciiSet = &AsciiSet {
    mask: [
        !0_u32, // C0: 0x00 to 0x1F (32 bits set)
        0,
        0,
        1 << (0x7F_u32 % 32), // DEL: 0x7F (one bit set)
    ],
};

macro_rules! static_assert {
    ($( $bool: expr, )+) => {
        fn _static_assert() {
            $(
                let _ = mem::transmute::<[u8; $bool as usize], u8>;
            )+
        }
    }
}

static_assert! {
    CONTROLS.contains(0x00),
    CONTROLS.contains(0x1F),
    !CONTROLS.contains(0x20),
    !CONTROLS.contains(0x7E),
    CONTROLS.contains(0x7F),
}

/// Everything that is not an ASCII letter or digit.
///
/// This is probably more eager than necessary in any context.
#[cfg_attr(creusot, ensures(NON_ALPHANUMERIC.mask_words()[0] == 0xffffffffu32 && NON_ALPHANUMERIC.mask_words()[1] == 0xfc00ffffu32 && NON_ALPHANUMERIC.mask_words()[2] == 0xf8000001u32 && NON_ALPHANUMERIC.mask_words()[3] == 0xf8000001u32))]
#[cfg_attr(creusot, bitwise_proof)]
pub const NON_ALPHANUMERIC: &AsciiSet = &CONTROLS
    .add(b' ')
    .add(b'!')
    .add(b'"')
    .add(b'#')
    .add(b'$')
    .add(b'%')
    .add(b'&')
    .add(b'\'')
    .add(b'(')
    .add(b')')
    .add(b'*')
    .add(b'+')
    .add(b',')
    .add(b'-')
    .add(b'.')
    .add(b'/')
    .add(b':')
    .add(b';')
    .add(b'<')
    .add(b'=')
    .add(b'>')
    .add(b'?')
    .add(b'@')
    .add(b'[')
    .add(b'\\')
    .add(b']')
    .add(b'^')
    .add(b'_')
    .add(b'`')
    .add(b'{')
    .add(b'|')
    .add(b'}')
    .add(b'~');

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_op() {
        let left = AsciiSet::EMPTY.add(b'A');
        let right = AsciiSet::EMPTY.add(b'B');
        let expected = AsciiSet::EMPTY.add(b'A').add(b'B');
        assert_eq!(left + right, expected);
    }

    #[test]
    fn not_op() {
        let set = AsciiSet::EMPTY.add(b'A').add(b'B');
        let not_set = !set;
        assert!(!not_set.contains(b'A'));
        assert!(not_set.contains(b'C'));
    }

    /// This test ensures that we can get the union of two sets as a constant value, which is
    /// useful for defining sets in a modular way.
    #[test]
    fn union() {
        const A: AsciiSet = AsciiSet::EMPTY.add(b'A');
        const B: AsciiSet = AsciiSet::EMPTY.add(b'B');
        const UNION: AsciiSet = A.union(B);
        const EXPECTED: AsciiSet = AsciiSet::EMPTY.add(b'A').add(b'B');
        assert_eq!(UNION, EXPECTED);
    }

    /// This test ensures that we can get the complement of a set as a constant value, which is
    /// useful for defining sets in a modular way.
    #[test]
    fn complement() {
        const BOTH: AsciiSet = AsciiSet::EMPTY.add(b'A').add(b'B');
        const COMPLEMENT: AsciiSet = BOTH.complement();
        assert!(!COMPLEMENT.contains(b'A'));
        assert!(!COMPLEMENT.contains(b'B'));
        assert!(COMPLEMENT.contains(b'C'));
    }
}
