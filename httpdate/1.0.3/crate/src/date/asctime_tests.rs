#[path = "../../../verification/trial/reference/date.rs"]
mod upstream;

use std::str::FromStr;
use std::time::SystemTime;

fn compare_with_upstream(input: &str) {
    let actual = crate::parse_http_date(input).ok();
    let expected = upstream::HttpDate::from_str(input)
        .ok()
        .map(SystemTime::from);
    assert_eq!(actual, expected, "input: {input:?}");
}

#[test]
fn asctime_valid_day_encodings_match_upstream() {
    for input in [
        "Sun Nov  6 08:49:37 1994",
        "Sun Nov 06 08:49:37 1994",
        "Wed Nov 16 08:49:37 1994",
    ] {
        compare_with_upstream(input);
        assert!(crate::parse_http_date(input).is_ok(), "input: {input:?}");
    }
}

#[test]
fn asctime_length_variations_match_upstream() {
    let fixture = "Sun Nov  6 08:49:37 1994";
    for end in 0..=fixture.len() {
        compare_with_upstream(&fixture[..end]);
    }
    for input in [
        " Sun Nov  6 08:49:37 1994",
        "Sun Nov  6 08:49:37 1994 ",
        "Sun Nov  6 08:49:37 19940",
        "Sun Nov  6 08:49:37 199",
    ] {
        compare_with_upstream(input);
    }
}

#[test]
fn asctime_all_ascii_single_byte_mutations_match_upstream() {
    let fixture = *b"Sun Nov  6 08:49:37 1994";
    for index in 0..fixture.len() {
        for replacement in 0u8..=127 {
            let mut bytes = fixture;
            bytes[index] = replacement;
            let input = std::str::from_utf8(&bytes).expect("ASCII mutation is UTF-8");
            compare_with_upstream(input);
        }
    }
}
