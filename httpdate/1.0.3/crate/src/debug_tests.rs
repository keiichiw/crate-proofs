// Native-only Debug regression module. It deliberately makes no
// formal-proof claim and constructs dates only through valid SystemTime values.
use std::fmt::{self, Debug};
use std::time::{Duration, UNIX_EPOCH};

use crate::date::HttpDate;

#[path = "../../verification/trial/reference/date.rs"]
mod upstream;

const YEAR_10000_START: u64 = 253_402_300_800;

fn public_date(seconds: u64) -> HttpDate {
    assert!(seconds < YEAR_10000_START);
    HttpDate::from(UNIX_EPOCH + Duration::from_secs(seconds))
}

fn reference_date(seconds: u64) -> upstream::HttpDate {
    assert!(seconds < YEAR_10000_START);
    upstream::HttpDate::from(UNIX_EPOCH + Duration::from_secs(seconds))
}

#[derive(Debug)]
#[allow(dead_code)] // The derived formatter reads these fields.
struct DateEnvelope<T> {
    label: &'static str,
    date: T,
}

#[derive(Debug)]
struct Error(());

fn assert_error_format(actual: &crate::Error, reference: &Error) {
    assert_eq!(format!("{:?}", actual), format!("{:?}", reference));
    assert_eq!(format!("{:#?}", actual), format!("{:#?}", reference));
    assert_eq!(format!("{:x?}", actual), format!("{:x?}", reference));
    assert_eq!(format!("{:#x?}", actual), format!("{:#x?}", reference));
    assert_eq!(format!("{:X?}", actual), format!("{:X?}", reference));
    assert_eq!(format!("{:#X?}", actual), format!("{:#X?}", reference));
    assert_eq!(format!("{:+?}", actual), format!("{:+?}", reference));
    assert_eq!(format!("{:08?}", actual), format!("{:08?}", reference));
    assert_eq!(format!("{:10?}", actual), format!("{:10?}", reference));
    assert_eq!(format!("{:.0?}", actual), format!("{:.0?}", reference));
    assert_eq!(format!("{:.1?}", actual), format!("{:.1?}", reference));
    assert_eq!(format!("{:.2?}", actual), format!("{:.2?}", reference));
    assert_eq!(format!("{:*>8?}", actual), format!("{:*>8?}", reference));
    assert_eq!(format!("{:_<8?}", actual), format!("{:_<8?}", reference));
    assert_eq!(format!("{:^10?}", actual), format!("{:^10?}", reference));
}

#[test]
fn debug_formatting_matches_upstream_for_valid_boundary_dates_and_error() {
    // Unix epoch, an established IMF date, leap day 2000, and the final
    // supported second. No invalid public records are manufactured.
    for seconds in [0, 784_111_777, 951_782_400, YEAR_10000_START - 1] {
        let actual = public_date(seconds);
        let reference = reference_date(seconds);

        assert_eq!(format!("{:?}", actual), format!("{:?}", reference));
        assert_eq!(format!("{:#?}", actual), format!("{:#?}", reference));
        assert_eq!(format!("{:x?}", actual), format!("{:x?}", reference));
        assert_eq!(format!("{:#x?}", actual), format!("{:#x?}", reference));
        assert_eq!(format!("{:X?}", actual), format!("{:X?}", reference));
        assert_eq!(format!("{:#X?}", actual), format!("{:#X?}", reference));
        assert_eq!(format!("{:+?}", actual), format!("{:+?}", reference));
        assert_eq!(format!("{:08?}", actual), format!("{:08?}", reference));
        assert_eq!(format!("{:10?}", actual), format!("{:10?}", reference));
        assert_eq!(format!("{:.0?}", actual), format!("{:.0?}", reference));
        assert_eq!(format!("{:.1?}", actual), format!("{:.1?}", reference));
        assert_eq!(format!("{:.2?}", actual), format!("{:.2?}", reference));
        assert_eq!(format!("{:*>8?}", actual), format!("{:*>8?}", reference));
        assert_eq!(format!("{:_<8?}", actual), format!("{:_<8?}", reference));
        assert_eq!(format!("{:^10?}", actual), format!("{:^10?}", reference));

        let actual_envelope = DateEnvelope {
            label: "date",
            date: actual,
        };
        let reference_envelope = DateEnvelope {
            label: "date",
            date: reference,
        };
        assert_eq!(
            format!("{:?}", actual_envelope),
            format!("{:?}", reference_envelope)
        );
        assert_eq!(
            format!("{:#?}", actual_envelope),
            format!("{:#?}", reference_envelope)
        );
        assert_eq!(
            format!("{:#10.1?}", actual_envelope),
            format!("{:#10.1?}", reference_envelope)
        );
    }

    let actual_error = crate::parse_http_date("not a date").unwrap_err();
    assert_error_format(&actual_error, &Error(()));
}

#[derive(Default, Debug, PartialEq, Eq)]
struct WriteTrace {
    attempted_chunks: Vec<String>,
    successful_writes: usize,
    fail_after: usize,
}

impl WriteTrace {
    fn with_failure_after(fail_after: usize) -> Self {
        Self {
            fail_after,
            ..Self::default()
        }
    }
}

impl fmt::Write for WriteTrace {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.attempted_chunks.push(text.to_owned());
        if self.successful_writes == self.fail_after {
            return Err(fmt::Error);
        }
        self.successful_writes += 1;
        Ok(())
    }
}

macro_rules! assert_write_trace_matches {
    ($format:literal, $actual:expr, $reference:expr) => {{
        for fail_after in 0..64 {
            let mut actual_trace = WriteTrace::with_failure_after(fail_after);
            let mut reference_trace = WriteTrace::with_failure_after(fail_after);
            let actual_result = fmt::write(&mut actual_trace, format_args!($format, $actual));
            let reference_result =
                fmt::write(&mut reference_trace, format_args!($format, $reference));
            assert_eq!(actual_result.is_err(), reference_result.is_err());
            assert_eq!(
                actual_trace, reference_trace,
                "format {:?}, fail after {fail_after}",
                $format
            );
        }
    }};
}

#[test]
fn debug_writer_chunks_and_failures_match_upstream() {
    let seconds = [0, 784_111_777, 951_782_400, YEAR_10000_START - 1];
    for seconds in seconds {
        let actual = public_date(seconds);
        let reference = reference_date(seconds);
        assert_write_trace_matches!("{:?}", actual, reference);
        assert_write_trace_matches!("{:#?}", actual, reference);
        assert_write_trace_matches!("{:#10.1?}", actual, reference);
    }

    let actual_error = crate::parse_http_date("not a date").unwrap_err();
    let reference_error = Error(());
    assert_write_trace_matches!("{:?}", actual_error, reference_error);
    assert_write_trace_matches!("{:#?}", actual_error, reference_error);
}
