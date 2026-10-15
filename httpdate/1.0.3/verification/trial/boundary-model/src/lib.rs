//! Candidate standard-library contracts, isolated from the verified crate.
//! Proofs here are conditional on the explicit assumptions below.
#![forbid(unsafe_code)]

use std::time::{SystemTime, UNIX_EPOCH};

#[cfg(creusot)]
use creusot_std::prelude::*;

/// Mathematical timestamp in nanoseconds, with an arbitrary fixed origin.
/// TRUSTED: supplied model of std::time::SystemTime; not a verified implementation.
#[cfg(creusot)]
#[trusted]
#[logic(opaque)]
pub fn time_ns(_t: SystemTime) -> Int {
    dead
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii(s: Seq<char>) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < s.len() ==> s[i]@ < 128 }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_whitespace(c: char) -> bool {
    pearlite! { c@ == 32 || (9 <= c@ && c@ <= 13) }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_trim_relation(input: Seq<char>, output: Seq<char>) -> bool {
    pearlite! {
        exists<lo: Int, hi: Int> 0 <= lo && lo <= hi && hi <= input.len()
        && output == input.subsequence(lo, hi)
        && (forall<i: Int> 0 <= i && i < lo ==> ascii_whitespace(input[i]))
        && (forall<i: Int> hi <= i && i < input.len() ==> ascii_whitespace(input[i]))
        && (lo == hi || (!ascii_whitespace(input[lo]) && !ascii_whitespace(input[hi - 1])))
    }
}

#[cfg(creusot)]
#[logic(open, inline)]
pub fn ascii_content(chars: Seq<char>, bytes: Seq<u8>) -> bool {
    pearlite! {
        chars.len() == bytes.len()
        && (forall<i: Int> 0 <= i && i < chars.len() ==> chars[i]@ == bytes[i]@)
    }
}

#[cfg(creusot)]
extern_spec! {
    // Opaque specification avoids translating platform-private Timespec fields.
    #[ensures(time_ns(std::time::UNIX_EPOCH) == 0)]
    const std::time::UNIX_EPOCH;

    impl std::time::SystemTime {
        // The bound excludes differences too large for std::time::Duration.
        #[requires(-18446744073709551615999999999 <= time_ns(*self) - time_ns(earlier)
            && time_ns(*self) - time_ns(earlier) <= 18446744073709551615999999999)]
        #[ensures(match result {
            Ok(d) => time_ns(*self) >= time_ns(earlier) && d@ == time_ns(*self) - time_ns(earlier),
            Err(_) => time_ns(*self) < time_ns(earlier),
        })]
        fn duration_since(&self, earlier: SystemTime) -> Result<std::time::Duration, std::time::SystemTimeError>;
    }

    mod std { mod str {
        // Deliberately restricted to ASCII; no assertion about invalid UTF-8.
        #[requires(forall<i: Int> 0 <= i && i < v@.len() ==> v@[i]@ < 128)]
        #[ensures(match result {
            Ok(s) => s@.len() == v@.len()
                && (forall<i: Int> 0 <= i && i < v@.len() ==> s@[i]@ == v@[i]@),
            Err(_) => false,
        })]
        fn from_utf8(v: &[u8]) -> Result<&str, std::str::Utf8Error>;
    } }

    impl str {
        #[ensures(result == ascii(self@))]
        fn is_ascii(&self) -> bool;

        // The parser rejects non-ASCII before reaching this restricted model.
        #[requires(ascii(self@))]
        #[ensures(ascii(result@) && ascii_trim_relation(self@, result@))]
        fn trim(&self) -> &str;

        #[requires(ascii(self@))]
        #[ensures(ascii_content(self@, result@))]
        fn as_bytes(&self) -> &[u8];
    }
}

// Linux 64-bit candidate only: the full httpdate range fits Unix Timespec's i64
// seconds. This is a stdlib assumption, reviewed against the pinned Rust source.
#[cfg(all(creusot, target_os = "linux", target_pointer_width = "64"))]
extern_spec! {
    impl std::ops::Add<std::time::Duration> for std::time::SystemTime {
        #[requires(time_ns(self) == 0 && rhs@ < 253402300800000000000)]
        #[ensures(time_ns(result) == time_ns(self) + rhs@)]
        fn add(self, rhs: std::time::Duration) -> std::time::SystemTime;
    }
}

/// Same successful path and truncation boundary as httpdate's SystemTime wrapper.
#[cfg_attr(creusot, requires(0 <= time_ns(t) - time_ns(UNIX_EPOCH)
    && time_ns(t) - time_ns(UNIX_EPOCH) < 253402300800000000000))]
#[cfg_attr(creusot, ensures(result@ == (time_ns(t) - time_ns(UNIX_EPOCH)) / 1000000000
    && result@ < 253402300800))]
pub fn bounded_epoch_seconds(t: SystemTime) -> u64 {
    let duration = t
        .duration_since(UNIX_EPOCH)
        .expect("all times should be after the epoch");
    let seconds = duration.as_secs();
    if seconds >= 253402300800 {
        panic!("date must be before year 9999");
    }
    seconds
}

/// Content preservation across the exact byte-to-text boundary used by Display.
#[cfg_attr(creusot, requires(forall<i: Int> 0 <= i && i < 29 ==> bytes@[i]@ < 128))]
#[cfg_attr(creusot, ensures(result@.len() == 29
    && (forall<i: Int> 0 <= i && i < 29 ==> result@[i]@ == bytes@[i]@)))]
pub fn ascii_text(bytes: &[u8; 29]) -> &str {
    std::str::from_utf8(bytes).unwrap()
}

/// Matches the public parser's ASCII check, whitespace trimming and byte access.
#[cfg_attr(creusot, ensures(match result {
    Some(bytes) => ascii(s@) && exists<trimmed: Seq<char>>
        ascii(trimmed) && ascii_trim_relation(s@, trimmed) && ascii_content(trimmed, bytes@),
    None => !ascii(s@),
}))]
pub fn normalized_ascii(s: &str) -> Option<&[u8]> {
    if !s.is_ascii() {
        return None;
    }
    Some(s.trim().as_bytes())
}

/// Same standard-library path as httpdate's inverse SystemTime wrapper.
#[cfg_attr(creusot, requires(seconds@ < 253402300800))]
#[cfg_attr(creusot, ensures(time_ns(result) == seconds@ * 1000000000))]
pub fn epoch_time(seconds: u64) -> SystemTime {
    UNIX_EPOCH + std::time::Duration::from_secs(seconds)
}

#[cfg_attr(creusot, requires(seconds@ < 253402300800))]
#[cfg_attr(creusot, ensures(result == seconds))]
pub fn time_boundary_roundtrip(seconds: u64) -> u64 {
    bounded_epoch_seconds(epoch_time(seconds))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn boundary_seconds_and_fractional_truncation() {
        for seconds in [0, 1, 86399, 86400, 951782400, 4107542400, 253402300799] {
            for nanos in [0, 1, 999999999] {
                let t = UNIX_EPOCH + Duration::new(seconds, nanos);
                assert_eq!(bounded_epoch_seconds(t), seconds);
                assert_eq!(
                    epoch_time(seconds),
                    UNIX_EPOCH + Duration::from_secs(seconds)
                );
                assert_eq!(time_boundary_roundtrip(seconds), seconds);
            }
        }
        for t in [
            UNIX_EPOCH - Duration::from_nanos(1),
            UNIX_EPOCH + Duration::from_secs(253402300800),
        ] {
            assert!(std::panic::catch_unwind(|| bounded_epoch_seconds(t)).is_err());
        }
    }

    #[test]
    fn all_ascii_values_preserve_content() {
        for value in 0..128 {
            let bytes = [value; 29];
            let text = ascii_text(&bytes);
            assert_eq!(text.as_bytes(), bytes);
            assert_eq!(text.chars().count(), 29);
            assert!(text.chars().all(|c| u32::from(c) == u32::from(value)));
        }
    }

    #[test]
    fn ascii_normalization_and_unicode_rejection() {
        let text = "Sun, 06 Nov 1994 08:49:37 GMT";
        assert_eq!(normalized_ascii(text), Some(text.as_bytes()));
        assert_eq!(normalized_ascii(""), Some(&b""[..]));
        for value in 0..128_u8 {
            let c = char::from(value);
            let padded = format!("{c}{text}{c}");
            let expected = if c.is_whitespace() {
                text.as_bytes()
            } else {
                padded.as_bytes()
            };
            assert_eq!(normalized_ascii(&padded), Some(expected));
            assert_eq!(c.is_whitespace(), value == 32 || (9..=13).contains(&value));
        }
        for text in ["é", "\u{a0}", "\u{2003}", "🌍"] {
            assert_eq!(normalized_ascii(text), None);
        }
    }
}
