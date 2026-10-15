//! Date and time utils for HTTP.
//!
//! Multiple HTTP header fields store timestamps.
//! For example a response created on May 15, 2015 may contain the header
//! `Date: Fri, 15 May 2015 15:34:21 GMT`. Since the timestamp does not
//! contain any timezone or leap second information it is equvivalent to
//! writing 1431696861 Unix time. Rust’s `SystemTime` is used to store
//! these timestamps.
//!
//! This crate provides two public functions:
//!
//! * `parse_http_date` to parse a HTTP datetime string to a system time
//! * `fmt_http_date` to format a system time to a IMF-fixdate
//!
//! In addition it exposes the `HttpDate` type that can be used to parse
//! and format timestamps. Convert a sytem time to `HttpDate` and vice versa.
//! The `HttpDate` (8 bytes) is smaller than `SystemTime` (16 bytes) and
//! using the display impl avoids a temporary allocation.
#![forbid(unsafe_code)]
// The private proof roots have no callers when other APIs are excluded.
#![cfg_attr(creusot, allow(dead_code))]

use std::error;
use std::fmt::{self, Debug, Display, Formatter};
use std::io;
use std::str::FromStr;
use std::time::SystemTime;

#[cfg(creusot)]
use creusot_std::prelude::*;
#[cfg(creusot)]
use stdlib_specs::time_ns;

#[cfg(creusot)]
mod stdlib_specs;

pub use date::HttpDate;

mod date;
mod debug_support;
use debug_support::*;
#[cfg(creusot)]
use stdlib_specs::{append_sink, debug_options, formatter_output, plain_options};

/// An opaque error type for all parsing errors.
pub struct Error(());

impl error::Error for Error {
    #[cfg_attr(creusot, ensures(result@.len() == 40))]
    #[cfg_attr(creusot, ensures(result@[0] == 'd' && result@[1] == 'e' && result@[2] == 's' && result@[3] == 'c' && result@[4] == 'r' && result@[5] == 'i' && result@[6] == 'p' && result@[7] == 't' && result@[8] == 'i' && result@[9] == 'o' && result@[10] == 'n' && result@[11] == '(' && result@[12] == ')' && result@[13] == ' ' && result@[14] == 'i' && result@[15] == 's' && result@[16] == ' ' && result@[17] == 'd' && result@[18] == 'e' && result@[19] == 'p' && result@[20] == 'r' && result@[21] == 'e' && result@[22] == 'c' && result@[23] == 'a' && result@[24] == 't' && result@[25] == 'e' && result@[26] == 'd' && result@[27] == ';' && result@[28] == ' ' && result@[29] == 'u' && result@[30] == 's' && result@[31] == 'e' && result@[32] == ' ' && result@[33] == 'D' && result@[34] == 'i' && result@[35] == 's' && result@[36] == 'p' && result@[37] == 'l' && result@[38] == 'a' && result@[39] == 'y'))]
    fn description(&self) -> &str {
        std::str::from_utf8(&[
            b'd', b'e', b's', b'c', b'r', b'i', b'p', b't', b'i', b'o', b'n', b'(', b')', b' ',
            b'i', b's', b' ', b'd', b'e', b'p', b'r', b'e', b'c', b'a', b't', b'e', b'd', b';',
            b' ', b'u', b's', b'e', b' ', b'D', b'i', b's', b'p', b'l', b'a', b'y',
        ])
        .unwrap()
    }

    #[cfg_attr(creusot, ensures(result == None))]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
    #[cfg_attr(creusot, ensures(result == None))]
    fn cause(&self) -> Option<&dyn std::error::Error> {
        None
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn error_message_bytes(s: Seq<u8>) -> bool {
    pearlite! { s.len() == 37 && s[0] == 115u8 && s[1] == 116u8 && s[2] == 114u8 && s[3] == 105u8 && s[4] == 110u8 && s[5] == 103u8 && s[6] == 32u8 && s[7] == 99u8 && s[8] == 111u8 && s[9] == 110u8 && s[10] == 116u8 && s[11] == 97u8 && s[12] == 105u8 && s[13] == 110u8 && s[14] == 115u8 && s[15] == 32u8 && s[16] == 110u8 && s[17] == 111u8 && s[18] == 32u8 && s[19] == 111u8 && s[20] == 114u8 && s[21] == 32u8 && s[22] == 97u8 && s[23] == 110u8 && s[24] == 32u8 && s[25] == 105u8 && s[26] == 110u8 && s[27] == 118u8 && s[28] == 97u8 && s[29] == 108u8 && s[30] == 105u8 && s[31] == 100u8 && s[32] == 32u8 && s[33] == 100u8 && s[34] == 97u8 && s[35] == 116u8 && s[36] == 101u8 }
}

impl Display for Error {
    #[cfg_attr(creusot, ensures(match result {
        Ok(()) => stdlib_specs::append_sink(*f) ==>
            exists<chars: Seq<char>, bytes: Seq<u8>> error_message_bytes(bytes) && stdlib_specs::ascii_content(chars, bytes)
            && stdlib_specs::formatter_output(^f) == stdlib_specs::formatter_output(*f).concat(chars),
        Err(_) => true,
    }))]
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        // Fixed ASCII message; scalar bytes avoid Creusot's byte-string literal ICE.
        let message = [
            b's', b't', b'r', b'i', b'n', b'g', b' ', b'c', b'o', b'n', b't', b'a', b'i', b'n',
            b's', b' ', b'n', b'o', b' ', b'o', b'r', b' ', b'a', b'n', b' ', b'i', b'n', b'v',
            b'a', b'l', b'i', b'd', b' ', b'd', b'a', b't', b'e',
        ];
        <Formatter<'_> as std::fmt::Write>::write_str(f, std::str::from_utf8(&message).unwrap())
    }
}

impl From<Error> for io::Error {
    #[cfg_attr(creusot, ensures(stdlib_specs::io_kind(result) == io::ErrorKind::Other))]
    #[cfg_attr(creusot, ensures(stdlib_specs::io_payload::<Error>(result) == Some(e)))]
    fn from(e: Error) -> io::Error {
        io::Error::new(io::ErrorKind::Other, e)
    }
}

/// Parse a date from an HTTP header field.
///
/// Supports the preferred IMF-fixdate and the legacy RFC 805 and
/// ascdate formats. Two digit years are mapped to dates between
/// 1970 and 2069.
#[cfg_attr(creusot, ensures(match result {
    Ok(t) => exists<d: date::RawDate> date::valid_calendar(d)
        && date::parsed_text(s@, d)
        && time_ns(t) == date::unix_seconds_model(d) * 1000000000,
    Err(_) => forall<d: date::RawDate> date::parsed_text(s@, d) ==> !date::valid_calendar(d),
}))]
pub fn parse_http_date(s: &str) -> Result<SystemTime, Error> {
    match HttpDate::from_str(s) {
        Ok(d) => Ok(SystemTime::from(d)),
        Err(error) => Err(error),
    }
}

/// Format a date to be used in a HTTP header field.
///
/// Dates are formatted as IMF-fixdate: `Fri, 15 May 2015 15:34:21 GMT`.
#[cfg_attr(creusot, requires(0 <= time_ns(d) && time_ns(d) < 253402300800000000000))]
#[cfg_attr(creusot, ensures(exists<raw: date::RawDate, bytes: Seq<u8>>
    date::valid_calendar(raw)
    && date::unix_seconds_model(raw) == time_ns(d) / 1000000000
    && date::imf_encoding(bytes, raw)
    && stdlib_specs::ascii_content(result@, bytes)))]
pub fn fmt_http_date(d: SystemTime) -> String {
    HttpDate::from(d).imf_string()
}

#[cfg(test)]
mod tests {
    use std::str;
    use std::time::{Duration, UNIX_EPOCH};

    use super::{fmt_http_date, parse_http_date, HttpDate};

    #[test]
    fn test_rfc_example() {
        let d = UNIX_EPOCH + Duration::from_secs(784111777);
        assert_eq!(
            d,
            parse_http_date("Sun, 06 Nov 1994 08:49:37 GMT").expect("#1")
        );
        assert_eq!(
            d,
            parse_http_date("Sunday, 06-Nov-94 08:49:37 GMT").expect("#2")
        );
        assert_eq!(d, parse_http_date("Sun Nov  6 08:49:37 1994").expect("#3"));
    }

    #[test]
    fn test2() {
        let d = UNIX_EPOCH + Duration::from_secs(1475419451);
        assert_eq!(
            d,
            parse_http_date("Sun, 02 Oct 2016 14:44:11 GMT").expect("#1")
        );
        assert!(parse_http_date("Sun Nov 10 08:00:00 1000").is_err());
        assert!(parse_http_date("Sun Nov 10 08*00:00 2000").is_err());
        assert!(parse_http_date("Sunday, 06-Nov-94 08+49:37 GMT").is_err());
    }

    #[test]
    fn test3() {
        let mut d = UNIX_EPOCH;
        assert_eq!(d, parse_http_date("Thu, 01 Jan 1970 00:00:00 GMT").unwrap());
        d += Duration::from_secs(3600);
        assert_eq!(d, parse_http_date("Thu, 01 Jan 1970 01:00:00 GMT").unwrap());
        d += Duration::from_secs(86400);
        assert_eq!(d, parse_http_date("Fri, 02 Jan 1970 01:00:00 GMT").unwrap());
        d += Duration::from_secs(2592000);
        assert_eq!(d, parse_http_date("Sun, 01 Feb 1970 01:00:00 GMT").unwrap());
        d += Duration::from_secs(2592000);
        assert_eq!(d, parse_http_date("Tue, 03 Mar 1970 01:00:00 GMT").unwrap());
        d += Duration::from_secs(31536005);
        assert_eq!(d, parse_http_date("Wed, 03 Mar 1971 01:00:05 GMT").unwrap());
        d += Duration::from_secs(15552000);
        assert_eq!(d, parse_http_date("Mon, 30 Aug 1971 01:00:05 GMT").unwrap());
        d += Duration::from_secs(6048000);
        assert_eq!(d, parse_http_date("Mon, 08 Nov 1971 01:00:05 GMT").unwrap());
        d += Duration::from_secs(864000000);
        assert_eq!(d, parse_http_date("Fri, 26 Mar 1999 01:00:05 GMT").unwrap());
    }

    #[test]
    fn test_fmt() {
        let d = UNIX_EPOCH;
        assert_eq!(fmt_http_date(d), "Thu, 01 Jan 1970 00:00:00 GMT");
        let d = UNIX_EPOCH + Duration::from_secs(1475419451);
        assert_eq!(fmt_http_date(d), "Sun, 02 Oct 2016 14:44:11 GMT");
    }

    #[allow(dead_code)]
    fn testcase(data: &[u8]) {
        if let Ok(s) = str::from_utf8(data) {
            println!("{:?}", s);
            if let Ok(d) = parse_http_date(s) {
                let o = fmt_http_date(d);
                assert!(!o.is_empty());
            }
        }
    }

    #[test]
    fn size_of() {
        assert_eq!(::std::mem::size_of::<HttpDate>(), 8);
    }

    #[test]
    fn test_date_comparison() {
        let a = UNIX_EPOCH + Duration::from_secs(784111777);
        let b = a + Duration::from_secs(30);
        assert!(a < b);
        let a_date: HttpDate = a.into();
        let b_date: HttpDate = b.into();
        assert!(a_date < b_date);
        assert_eq!(a_date.cmp(&b_date), ::std::cmp::Ordering::Less)
    }

    #[test]
    fn test_parse_bad_date() {
        // 1994-11-07 is actually a Monday
        let parsed = "Sun, 07 Nov 1994 08:48:37 GMT".parse::<HttpDate>();
        assert!(parsed.is_err())
    }
}

#[cfg(creusot)]
#[ensures(result)]
fn error_conversion_observable(e: Error) -> bool {
    let converted = io::Error::from(e);
    match converted.kind() {
        io::ErrorKind::Other => true,
        _ => false,
    }
}

#[cfg(test)]
mod error_tests;

#[cfg(creusot)]
#[logic(open(self), inline)]
fn error_debug_chars(pretty: bool) -> Seq<char> {
    if pretty {
        seq!['E', 'r', 'r', 'o', 'r', '(', '\n', ' ', ' ', ' ', ' ', '(', ')', ',', '\n', ')']
    } else {
        seq!['E', 'r', 'r', 'o', 'r', '(', '(', ')', ')']
    }
}
impl Debug for Error {
    #[cfg_attr(creusot, ensures(match result {
        Ok(()) => plain_options(debug_options(*f)) && append_sink(*f) ==>
            formatter_output(^f) == formatter_output(*f).concat(error_debug_chars(debug_options(*f).flags == 4u32)),
        Err(_) => true,
    }))]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let pretty = match debug_mode(f) {
            Some(pretty) => pretty,
            None => return f.debug_tuple("Error").field(&self.0).finish(),
        };
        write_ascii(f, &[b'E', b'r', b'r', b'o', b'r'])?;
        if pretty {
            write_ascii(f, &[b'(', b'\n'])?;
            write_ascii(f, &[b' ', b' ', b' ', b' '])?;
        } else {
            write_ascii(f, &[b'('])?;
        }
        <() as Debug>::fmt(&self.0, f)?;
        if pretty {
            write_ascii(f, &[b',', b'\n'])?;
        }
        write_ascii(f, &[b')'])
    }
}

#[cfg(test)]
mod debug_tests;
