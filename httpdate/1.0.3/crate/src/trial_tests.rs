use super::{from_unix_seconds, imf_bytes, to_unix_seconds, HttpDate};
use std::cmp::Ordering;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[path = "../../verification/trial/reference/date.rs"]
mod upstream;

const YEAR_10000_START: u64 = 253_402_300_800;
const DAY: u64 = 86_400;

fn assert_matches_upstream(seconds: u64) {
    assert!(seconds < YEAR_10000_START);
    let instant = UNIX_EPOCH + Duration::from_secs(seconds);
    let current = from_unix_seconds(seconds);
    let reference = upstream::HttpDate::from(instant);

    assert_eq!(
        std::str::from_utf8(&imf_bytes(&current)).unwrap(),
        reference.to_string(),
        "formatted output at Unix second {seconds}"
    );
    assert_eq!(to_unix_seconds(current), seconds, "inverse at {seconds}");
    let text = reference.to_string();
    assert_eq!(
        crate::parse_http_date(&text).unwrap(),
        instant,
        "public validation of canonical date at {seconds}"
    );
    assert_eq!(
        SystemTime::from(reference),
        instant,
        "upstream baseline round trip at {seconds}"
    );
}

fn assert_rfc850_matches_upstream(input: &str) {
    use std::str::FromStr;

    let actual = crate::parse_http_date(input).ok();
    let expected = upstream::HttpDate::from_str(input)
        .ok()
        .map(SystemTime::from);
    assert_eq!(actual, expected, "RFC850 parser difference for {input:?}");
}

fn hash_with_default_hasher<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

fn assert_public_traits_match_upstream(seconds: u64) {
    let instant = UNIX_EPOCH + Duration::from_secs(seconds);
    let current = HttpDate::from(instant);
    let reference = upstream::HttpDate::from(instant);

    assert_eq!(format!("{current:?}"), format!("{reference:?}"));
    assert_eq!(
        hash_with_default_hasher(&current),
        hash_with_default_hasher(&reference),
        "hash at Unix second {seconds}"
    );
}

#[test]
fn public_httpdate_traits_match_upstream_for_valid_dates() {
    // Include epoch/day boundaries, Gregorian leap-century transitions, and
    // the final supported second. Adjacent pairs exercise chronological order.
    let seconds = [
        0,
        1,
        DAY - 1,
        DAY,
        946_684_799,     // final second of 1999
        946_684_800,     // 2000-01-01
        951_696_000,     // 2000-02-28
        951_782_400,     // 2000-02-29
        951_868_799,     // final second of 2000-02-29
        951_868_800,     // 2000-03-01
        4_107_455_999,   // final second of 2100-02-27
        4_107_456_000,   // 2100-02-28
        4_107_542_399,   // final second of 2100-02-28
        4_107_542_400,   // 2100-03-01
        13_574_563_200,  // 2400-02-29
        13_574_649_599,  // final second of 2400-02-29
        13_574_649_600,  // 2400-03-01
        253_370_764_799, // final second of 9998
        253_370_764_800, // 9999-01-01
        YEAR_10000_START - 1,
    ];

    for &second in &seconds {
        assert_public_traits_match_upstream(second);
        // Equal copies must remain equal, with the same total-order behavior.
        let instant = UNIX_EPOCH + Duration::from_secs(second);
        let a = HttpDate::from(instant);
        let b = HttpDate::from(instant);
        assert_eq!(a, b);
        assert_eq!(a.partial_cmp(&b), Some(Ordering::Equal));
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    for pair in seconds.windows(2) {
        let left_time = UNIX_EPOCH + Duration::from_secs(pair[0]);
        let right_time = UNIX_EPOCH + Duration::from_secs(pair[1]);
        let left = HttpDate::from(left_time);
        let right = HttpDate::from(right_time);
        let reference_left = upstream::HttpDate::from(left_time);
        let reference_right = upstream::HttpDate::from(right_time);

        assert_eq!(left == right, reference_left == reference_right);
        assert_eq!(
            left.partial_cmp(&right),
            reference_left.partial_cmp(&reference_right)
        );
        assert_eq!(left.cmp(&right), reference_left.cmp(&reference_right));
    }
}

#[test]
fn public_fmt_http_date_matches_upstream_at_boundaries_and_subseconds() {
    for seconds in [
        0,
        1,
        DAY - 1,
        DAY,
        946_684_799,
        946_684_800,
        951_782_400,    // leap day in 2000
        4_107_542_400,  // 2100-03-01, after a non-leap century
        13_574_563_200, // leap day in 2400
        253_370_764_799,
        253_370_764_800,
        YEAR_10000_START - 1,
    ] {
        let whole_second = UNIX_EPOCH + Duration::from_secs(seconds);
        for nanos in [0, 1, 999_999_999] {
            let instant = whole_second + Duration::from_nanos(nanos);
            let reference = upstream::HttpDate::from(instant);
            assert_eq!(
                crate::fmt_http_date(instant),
                reference.to_string(),
                "formatted output at Unix second {seconds} plus {nanos} ns"
            );
        }
    }
}

#[test]
fn error_display_and_io_conversion_keep_the_public_message_and_kind() {
    let error = crate::parse_http_date("not a date").unwrap_err();
    let message = "string contains no or an invalid date";
    assert_eq!(error.to_string(), message);

    let io_error: std::io::Error = error.into();
    assert_eq!(io_error.kind(), std::io::ErrorKind::Other);
    assert_eq!(io_error.to_string(), message);
}

#[derive(Default)]
struct CaptureWriter(String);

impl std::fmt::Write for CaptureWriter {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.0.push_str(text);
        Ok(())
    }
}

struct FailingWriter;

impl std::fmt::Write for FailingWriter {
    fn write_str(&mut self, _text: &str) -> std::fmt::Result {
        Err(std::fmt::Error)
    }
}

#[test]
fn display_writes_to_custom_sinks_and_propagates_sink_errors() {
    let error = crate::parse_http_date("not a date").unwrap_err();
    let mut error_output = CaptureWriter::default();
    assert_eq!(
        std::fmt::write(&mut error_output, format_args!("{error}")),
        Ok(())
    );
    assert_eq!(error_output.0, "string contains no or an invalid date");

    let date = HttpDate::from(UNIX_EPOCH);
    let mut date_output = CaptureWriter::default();
    assert_eq!(
        std::fmt::write(&mut date_output, format_args!("{date}")),
        Ok(())
    );
    assert_eq!(date_output.0, "Thu, 01 Jan 1970 00:00:00 GMT");

    assert!(std::fmt::write(&mut FailingWriter, format_args!("{error}")).is_err());
    assert!(std::fmt::write(&mut FailingWriter, format_args!("{date}")).is_err());
}

#[test]
fn extracted_conversion_and_formatter_match_upstream_on_every_day() {
    // One representative instant on every civil day in the full supported range.
    // The 12:34:56 sample covers every date/weekday without duplicating
    // millions of equivalent time-of-day cases.
    let seconds_after_midnight = 12 * 3_600 + 34 * 60 + 56;
    for midnight in (0..YEAR_10000_START).step_by(DAY as usize) {
        assert_matches_upstream(midnight + seconds_after_midnight);
    }
}

#[test]
fn extracted_conversion_matches_upstream_at_time_and_calendar_boundaries() {
    for seconds in [
        0,
        1,
        DAY - 1,
        DAY,
        951_696_000,    // 2000-02-28
        951_782_400,    // 2000-02-29
        951_868_800,    // 2000-03-01
        4_107_456_000,  // 2100-02-28
        4_107_542_400,  // 2100-03-01
        13_574_563_200, // 2400-02-29
        13_574_649_600, // 2400-03-01
        YEAR_10000_START - 1,
    ] {
        assert_matches_upstream(seconds);
    }
}

#[test]
fn native_system_time_wrappers_preserve_panics_and_truncate_subseconds() {
    let before_epoch = UNIX_EPOCH - Duration::from_secs(1);
    assert!(std::panic::catch_unwind(|| HttpDate::from(before_epoch)).is_err());

    let year_10000 = UNIX_EPOCH + Duration::from_secs(YEAR_10000_START);
    assert!(std::panic::catch_unwind(|| HttpDate::from(year_10000)).is_err());
    assert!(std::panic::catch_unwind(|| crate::fmt_http_date(year_10000)).is_err());

    for seconds in [0, 951_782_400, YEAR_10000_START - 1] {
        let whole_second = UNIX_EPOCH + Duration::from_secs(seconds);
        for nanos in [0, 1, 999_999_999] {
            let precise = whole_second + Duration::from_nanos(nanos);
            let date = HttpDate::from(precise);
            assert_eq!(to_unix_seconds(date.as_raw()), seconds);
            assert_eq!(SystemTime::from(date), whole_second);
            assert_eq!(
                crate::fmt_http_date(precise),
                crate::fmt_http_date(whole_second),
                "fractional second {nanos} at Unix second {seconds}"
            );
        }
    }
}

#[test]
fn public_parser_preserves_legacy_year_padding_and_ascii_trim_behavior() {
    assert_eq!(
        crate::parse_http_date("Wednesday, 06-Nov-69 08:49:37 GMT").unwrap(),
        UNIX_EPOCH + Duration::from_secs(3_150_953_377)
    );
    assert_eq!(
        crate::parse_http_date("Friday, 06-Nov-70 08:49:37 GMT").unwrap(),
        UNIX_EPOCH + Duration::from_secs(26_729_377)
    );
    assert_eq!(
        crate::parse_http_date("Tue Feb 29 00:00:00 2000").unwrap(),
        UNIX_EPOCH + Duration::from_secs(951_782_400)
    );
    assert_eq!(
        crate::parse_http_date("\tSun, 06 Nov 1994 08:49:37 GMT\r\n").unwrap(),
        UNIX_EPOCH + Duration::from_secs(784_111_777)
    );
    assert!(crate::parse_http_date("\u{00a0}Sun, 06 Nov 1994 08:49:37 GMT").is_err());
}

#[test]
fn extracted_validator_matches_upstream_on_valid_and_invalid_calendar_fields() {
    use std::str::FromStr;
    let months = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let weekdays = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    let compare = |text: String| {
        let actual = crate::parse_http_date(&text).ok();
        let expected = upstream::HttpDate::from_str(&text)
            .ok()
            .map(SystemTime::from);
        assert_eq!(actual, expected, "validator difference for {text}");
    };
    for year in [
        0, 1969, 1970, 1971, 1999, 2000, 2004, 2099, 2100, 2399, 2400, 9999,
    ] {
        for month in months {
            for day in 0..=35 {
                for weekday in weekdays {
                    compare(format!(
                        "{weekday}, {day:02} {month} {year:04} 12:34:56 GMT"
                    ));
                }
            }
        }
    }
    for hour in [0, 23, 24, 59, 60, 99] {
        for minute in [0, 59, 60, 99] {
            for second in [0, 59, 60, 99] {
                compare(format!(
                    "Thu, 01 Jan 1970 {hour:02}:{minute:02}:{second:02} GMT"
                ));
            }
        }
    }
}

#[test]
fn public_rfc850_parser_matches_upstream_prefix_pivot_and_mutation_behavior() {
    let valid_1994 = [
        "Monday, 07-Nov-94 08:49:37 GMT",
        "Tuesday, 08-Nov-94 08:49:37 GMT",
        "Wednesday, 09-Nov-94 08:49:37 GMT",
        "Thursday, 10-Nov-94 08:49:37 GMT",
        "Friday, 11-Nov-94 08:49:37 GMT",
        "Saturday, 12-Nov-94 08:49:37 GMT",
        "Sunday, 06-Nov-94 08:49:37 GMT",
    ];
    for input in valid_1994 {
        assert_rfc850_matches_upstream(input);
        assert!(crate::parse_http_date(input).is_ok(), "fixture: {input}");
    }

    // These dates pin both branches of the source's fixed 70 pivot.
    let pivot_fixtures = [
        "Wednesday, 06-Nov-69 08:49:37 GMT",
        "Friday, 06-Nov-70 08:49:37 GMT",
    ];
    for input in pivot_fixtures {
        assert_rfc850_matches_upstream(input);
        assert!(crate::parse_http_date(input).is_ok(), "fixture: {input}");
    }

    // The original parser leaves the byte between year and hour unchecked.
    let unchecked_separator = "Sunday, 06-Nov-94x08:49:37 GMT";
    assert_rfc850_matches_upstream(unchecked_separator);
    assert!(crate::parse_http_date(unchecked_separator).is_ok());

    let length_fixtures = [valid_1994[0], valid_1994[6], pivot_fixtures[0]];
    for fixture in length_fixtures {
        for end in 0..=fixture.len() {
            assert_rfc850_matches_upstream(&fixture[..end]);
        }
        for input in [format!("{fixture}x"), fixture[1..].to_string()] {
            assert_rfc850_matches_upstream(&input);
        }
    }

    // Exercise every ASCII replacement at every byte position on two valid
    // examples, including the long weekday prefix and the 69 pivot branch.
    for fixture in [valid_1994[6], pivot_fixtures[0]] {
        let original = fixture.as_bytes();
        for index in 0..original.len() {
            for replacement in 0u8..=127 {
                let mut bytes = original.to_vec();
                bytes[index] = replacement;
                let input = std::str::from_utf8(&bytes).expect("ASCII mutation is UTF-8");
                assert_rfc850_matches_upstream(input);
            }
        }
    }
}
