//! Independent, minimal reproductions of three extractor boundaries seen in ipnet.
//! These functions are diagnostic examples, not replacement ipnet implementations.

use core::fmt;

#[derive(Default)]
pub struct Sink {
    pub writes: usize,
}

impl fmt::Write for Sink {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        self.writes += 1;
        Ok(())
    }
}

/// Requires a mutable unsize from `&mut Sink` to `&mut dyn fmt::Write`.
/// The write must update the original `sink.writes` through that borrow.
pub fn mutable_dyn_write(sink: &mut Sink) -> fmt::Result {
    fmt::write(sink, format_args!("{}", 7u8))
}

pub struct Cursor<'a> {
    pub bytes: &'a [u8],
    pub pos: usize,
}

/// The callback may mutate the borrowed cursor. On `None`, pos rolls back.
pub fn borrowed_callback<T, F>(cursor: &mut Cursor<'_>, callback: F) -> Option<T>
where
    F: FnOnce(&mut Cursor<'_>) -> Option<T>,
{
    let old = cursor.pos;
    let result = callback(cursor);
    if result.is_none() {
        cursor.pos = old;
    }
    result
}

pub fn next_ascii(cursor: &mut Cursor<'_>) -> Option<u8> {
    borrowed_callback(cursor, |c| {
        let byte = *c.bytes.get(c.pos)?;
        c.pos += 1;
        Some(byte)
    })
}

/// An independent Vec::extend closure probe for the aggregate dependency.
pub fn extend_bytes(dst: &mut Vec<u8>, src: &[u8]) {
    dst.extend(src.iter().copied());
}
