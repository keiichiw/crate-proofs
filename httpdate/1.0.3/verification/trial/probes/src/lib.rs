#![forbid(unsafe_code)]
#[cfg(creusot)]
use creusot_std::prelude::{ensures, requires, Int};

#[cfg(feature = "probe-duration")]
#[cfg_attr(creusot, ensures(result.0@ * 1_000_000_000 + result.1@ == d@ && result.1@ < 1_000_000_000))]
pub fn duration_parts(d: std::time::Duration) -> (u64, u32) {
    (d.as_secs(), d.subsec_nanos())
}

#[cfg(feature = "probe-system-time")]
pub fn epoch_seconds(t: std::time::SystemTime) -> Result<u64, std::time::SystemTimeError> {
    match t.duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => Ok(d.as_secs()),
        Err(e) => Err(e),
    }
}

#[cfg(feature = "probe-utf8")]
#[cfg_attr(creusot, requires(forall<i: Int> 0 <= i && i < 29 ==> bytes@[i]@ < 128))]
#[cfg_attr(creusot, ensures(result))]
pub fn ascii_is_utf8(bytes: [u8; 29]) -> bool {
    std::str::from_utf8(&bytes).is_ok()
}

#[cfg(feature = "probe-string")]
pub fn ascii_trimmed_empty(s: &str) -> bool {
    s.is_ascii() && s.trim().is_empty()
}

#[cfg(feature = "probe-formatter")]
pub fn formatter_write(f: &mut std::fmt::Formatter<'_>, s: &str) -> std::fmt::Result {
    f.write_str(s)
}
