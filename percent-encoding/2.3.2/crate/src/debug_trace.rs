//! Checked observation of the requests made through `DebugStruct`.
//!
//! The trace records the builder's struct name, ordered fields, typed values,
//! and the result returned by `finish`. It does not model rendered text or
//! formatter/writer state.

use core::{fmt, slice};

use crate::AsciiSet;
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(creusot)]
pub(crate) struct DebugTrace<'a> {
    pub(crate) struct_name: &'a str,
    /// Field names and type tags share positions, preserving call order.
    pub(crate) field_names: Seq<&'a str>,
    pub(crate) field_type_tags: Seq<u8>,
    /// Typed values are kept in separate channels; each channel follows the
    /// occurrence order of its corresponding tag.
    pub(crate) word_values: Seq<Snapshot<Seq<u32>>>,
    pub(crate) byte_values: Seq<Snapshot<Seq<u8>>>,
    pub(crate) iter_values: Seq<Snapshot<Seq<u8>>>,
    pub(crate) ascii_set_values: Seq<Snapshot<Seq<u32>>>,
    pub(crate) finish_status: Option<bool>,
}

#[cfg(creusot)]
impl<'a> DebugTrace<'a> {
    pub(crate) fn empty(name: &'a str) -> Ghost<Self> {
        ghost! {
            Self {
                struct_name: name,
                field_names: Seq::new().into_inner(),
                field_type_tags: Seq::new().into_inner(),
                word_values: Seq::new().into_inner(),
                byte_values: Seq::new().into_inner(),
                iter_values: Seq::new().into_inner(),
                ascii_set_values: Seq::new().into_inner(),
                finish_status: None,
            }
        }
    }
}

// These are signature-only standard-library models. In particular, they make
// no claim about builder state, rendered output, or `dyn Debug` interpretation.
#[cfg(creusot)]
extern_spec! {
    impl<'a> fmt::Formatter<'a> {
        fn debug_struct<'b>(&'b mut self, name: &str) -> fmt::DebugStruct<'b, 'a>;
    }

    impl<'a, 'b: 'a> fmt::DebugStruct<'a, 'b> {
        fn field<'c>(&'c mut self, name: &str, value: &dyn fmt::Debug) -> &'c mut Self;
        fn finish(&mut self) -> fmt::Result;
    }
}

#[cfg_attr(creusot, ensures((^*trace).struct_name == name && (^*trace).field_names.len() == 0 && (^*trace).field_type_tags.len() == 0 && (^*trace).word_values.len() == 0 && (^*trace).byte_values.len() == 0 && (^*trace).iter_values.len() == 0 && (^*trace).ascii_set_values.len() == 0 && (^*trace).finish_status == None))]
pub(crate) fn start<'f, 'a, 'b, 't>(
    formatter: &'f mut fmt::Formatter<'b>,
    name: &'a str,
    #[cfg(creusot)] mut trace: Ghost<&'t mut DebugTrace<'a>>,
) -> fmt::DebugStruct<'f, 'b>
where
    'a: 't,
{
    let builder = formatter.debug_struct(name);
    #[cfg(creusot)]
    ghost! {
        (**trace).struct_name = name;
        (**trace).field_names = Seq::new().into_inner();
        (**trace).field_type_tags = Seq::new().into_inner();
        (**trace).word_values = Seq::new().into_inner();
        (**trace).byte_values = Seq::new().into_inner();
        (**trace).iter_values = Seq::new().into_inner();
        (**trace).ascii_set_values = Seq::new().into_inner();
        (**trace).finish_status = None;
    };
    builder
}

#[cfg_attr(creusot, ensures((^*trace).field_names == (**trace).field_names.push_back(name)))]
#[cfg_attr(creusot, ensures((^*trace).field_type_tags == (**trace).field_type_tags.push_back(0u8)))]
#[cfg_attr(creusot, ensures((^*trace).word_values == (**trace).word_values.push_back(Snapshot::new(value@))))]
#[cfg_attr(creusot, ensures((^*trace).struct_name == (**trace).struct_name && (^*trace).byte_values == (**trace).byte_values && (^*trace).iter_values == (**trace).iter_values && (^*trace).ascii_set_values == (**trace).ascii_set_values && (^*trace).finish_status == (**trace).finish_status))]
pub(crate) fn field_words<'a, 't>(
    builder: &mut fmt::DebugStruct<'_, '_>,
    name: &'a str,
    value: &[u32; 4],
    #[cfg(creusot)] mut trace: Ghost<&'t mut DebugTrace<'a>>,
) where
    'a: 't,
{
    builder.field(name, value);
    #[cfg(creusot)]
    let value_model = snapshot!(value@);
    #[cfg(creusot)]
    ghost! {
        (**trace).field_names.push_back_ghost(name);
        (**trace).field_type_tags.push_back_ghost(0u8);
        (**trace).word_values.push_back_ghost(value_model);
    };
}

#[cfg_attr(creusot, ensures((^*trace).field_names == (**trace).field_names.push_back(name)))]
#[cfg_attr(creusot, ensures((^*trace).field_type_tags == (**trace).field_type_tags.push_back(1u8)))]
#[cfg_attr(creusot, ensures((^*trace).byte_values == (**trace).byte_values.push_back(Snapshot::new(value@))))]
#[cfg_attr(creusot, ensures((^*trace).struct_name == (**trace).struct_name && (^*trace).word_values == (**trace).word_values && (^*trace).iter_values == (**trace).iter_values && (^*trace).ascii_set_values == (**trace).ascii_set_values && (^*trace).finish_status == (**trace).finish_status))]
pub(crate) fn field_bytes<'a, 't>(
    builder: &mut fmt::DebugStruct<'_, '_>,
    name: &'a str,
    value: &[u8],
    #[cfg(creusot)] mut trace: Ghost<&'t mut DebugTrace<'a>>,
) where
    'a: 't,
{
    builder.field(name, &value);
    #[cfg(creusot)]
    let value_model = snapshot!(value@);
    #[cfg(creusot)]
    ghost! {
        (**trace).field_names.push_back_ghost(name);
        (**trace).field_type_tags.push_back_ghost(1u8);
        (**trace).byte_values.push_back_ghost(value_model);
    };
}

#[cfg_attr(creusot, ensures((^*trace).field_names == (**trace).field_names.push_back(name)))]
#[cfg_attr(creusot, ensures((^*trace).field_type_tags == (**trace).field_type_tags.push_back(2u8)))]
#[cfg_attr(creusot, ensures((^*trace).iter_values == (**trace).iter_values.push_back(Snapshot::new(value@@))))]
#[cfg_attr(creusot, ensures((^*trace).struct_name == (**trace).struct_name && (^*trace).word_values == (**trace).word_values && (^*trace).byte_values == (**trace).byte_values && (^*trace).ascii_set_values == (**trace).ascii_set_values && (^*trace).finish_status == (**trace).finish_status))]
pub(crate) fn field_byte_iter<'a, 't>(
    builder: &mut fmt::DebugStruct<'_, '_>,
    name: &'a str,
    value: &slice::Iter<'_, u8>,
    #[cfg(creusot)] mut trace: Ghost<&'t mut DebugTrace<'a>>,
) where
    'a: 't,
{
    builder.field(name, value);
    #[cfg(creusot)]
    let value_model = snapshot!(value@@);
    #[cfg(creusot)]
    ghost! {
        (**trace).field_names.push_back_ghost(name);
        (**trace).field_type_tags.push_back_ghost(2u8);
        (**trace).iter_values.push_back_ghost(value_model);
    };
}

#[cfg_attr(creusot, ensures((^*trace).field_names == (**trace).field_names.push_back(name)))]
#[cfg_attr(creusot, ensures((^*trace).field_type_tags == (**trace).field_type_tags.push_back(3u8)))]
#[cfg_attr(creusot, ensures((^*trace).ascii_set_values == (**trace).ascii_set_values.push_back(Snapshot::new(value.mask_words()))))]
#[cfg_attr(creusot, ensures((^*trace).struct_name == (**trace).struct_name && (^*trace).word_values == (**trace).word_values && (^*trace).byte_values == (**trace).byte_values && (^*trace).iter_values == (**trace).iter_values && (^*trace).finish_status == (**trace).finish_status))]
pub(crate) fn field_ascii_set<'a, 't>(
    builder: &mut fmt::DebugStruct<'_, '_>,
    name: &'a str,
    value: &AsciiSet,
    #[cfg(creusot)] mut trace: Ghost<&'t mut DebugTrace<'a>>,
) where
    'a: 't,
{
    builder.field(name, value);
    #[cfg(creusot)]
    let value_model = snapshot!(value.mask_words());
    #[cfg(creusot)]
    ghost! {
        (**trace).field_names.push_back_ghost(name);
        (**trace).field_type_tags.push_back_ghost(3u8);
        (**trace).ascii_set_values.push_back_ghost(value_model);
    };
}

#[cfg_attr(creusot, ensures((^*trace).finish_status == Some(match result { Ok(()) => true, Err(_) => false }) && (^*trace).struct_name == (**trace).struct_name && (^*trace).field_names == (**trace).field_names && (^*trace).field_type_tags == (**trace).field_type_tags && (^*trace).word_values == (**trace).word_values && (^*trace).byte_values == (**trace).byte_values && (^*trace).iter_values == (**trace).iter_values && (^*trace).ascii_set_values == (**trace).ascii_set_values))]
pub(crate) fn finish(
    builder: &mut fmt::DebugStruct<'_, '_>,
    #[cfg(creusot)] mut trace: Ghost<&mut DebugTrace<'_>>,
) -> fmt::Result {
    let result = builder.finish();
    #[cfg(creusot)]
    ghost! {
        (**trace).finish_status = Some(matches!(result, Ok(())));
    };
    result
}
