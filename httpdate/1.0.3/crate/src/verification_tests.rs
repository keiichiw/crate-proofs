use super::{parse_imf_fixdate, toint_1, toint_2, toint_4};

#[test]
fn decimal_helpers_match_ascii_digit_specification() {
    for byte in 0u16..=255 {
        let byte = byte as u8;
        let expected = if byte.is_ascii_digit() {
            Ok(byte - b'0')
        } else {
            Err(())
        };
        assert_eq!(toint_1(byte).map_err(|_| ()), expected, "byte {byte}");
    }

    for high in 0u16..=255 {
        for low in 0u16..=255 {
            let pair = [high as u8, low as u8];
            let expected = if pair.iter().all(u8::is_ascii_digit) {
                Ok(u16::from(pair[0] - b'0') * 10 + u16::from(pair[1] - b'0'))
            } else {
                Err(())
            };
            assert_eq!(
                toint_2(&pair).map(u16::from).map_err(|_| ()),
                expected,
                "bytes {pair:?}"
            );
        }
    }

    for value in 0u16..=9999 {
        let text = format!("{value:04}");
        assert_eq!(toint_4(text.as_bytes()).unwrap(), value, "text {text}");
    }

    // At every position, exhaust the byte domain and reject every non-digit.
    for position in 0..4 {
        for invalid in 0u16..=255 {
            let invalid = invalid as u8;
            if invalid.is_ascii_digit() {
                continue;
            }
            let mut bytes = *b"1234";
            bytes[position] = invalid;
            assert!(
                toint_4(&bytes).is_err(),
                "position {position}, byte {invalid}"
            );
        }
    }

    // Slices may be longer than the required digit count; only their prefix is read.
    assert_eq!(toint_2(b"12x").unwrap(), 12);
    assert_eq!(toint_4(b"1234x").unwrap(), 1234);
}

#[test]
fn imf_fixdate_parser_extracts_fixture_fields() {
    let parsed = parse_imf_fixdate(b"Sun, 06 Nov 1994 08:49:37 GMT").unwrap();
    assert_eq!(parsed.wday, 7);
    assert_eq!(parsed.day, 6);
    assert_eq!(parsed.mon, 11);
    assert_eq!(parsed.year, 1994);
    assert_eq!(parsed.hour, 8);
    assert_eq!(parsed.min, 49);
    assert_eq!(parsed.sec, 37);
}

#[test]
fn imf_fixdate_parser_handles_arbitrary_lengths_without_panicking() {
    for len in 0..=100 {
        let samples = [0, b' ', 0x80, 0xff];
        for byte in samples {
            let input = vec![byte; len];
            let _ = parse_imf_fixdate(&input);
        }

        let input: Vec<u8> = (0..len)
            .map(|index| (index.wrapping_mul(37).wrapping_add(len * 11) & 0xff) as u8)
            .collect();
        let _ = parse_imf_fixdate(&input);
    }
}

#[test]
fn imf_fixdate_parser_handles_single_byte_substitutions_without_panicking() {
    let fixture = *b"Sun, 06 Nov 1994 08:49:37 GMT";
    for position in 0..fixture.len() {
        for byte in 0u16..=255 {
            let mut input = fixture;
            input[position] = byte as u8;
            let _ = parse_imf_fixdate(&input);
        }
    }
}

#[test]
fn imf_fixdate_parser_rejects_malformed_delimiters_and_names() {
    for (position, replacement) in [
        (3, b';'),
        (16, b'-'),
        (19, b'.'),
        (22, b';'),
        (28, b'!'),
        (8, b'X'), // month
        (0, b'X'), // weekday
    ] {
        let mut input = *b"Sun, 06 Nov 1994 08:49:37 GMT";
        input[position] = replacement;
        assert!(
            parse_imf_fixdate(&input).is_err(),
            "position {position}, replacement {replacement}"
        );
    }
}

#[test]
fn raw_parser_accepts_syntax_fields_while_public_parser_checks_calendar_ranges() {
    let with_second_99 = b"Sun, 06 Nov 1994 08:49:99 GMT";
    let raw = parse_imf_fixdate(with_second_99).unwrap();
    assert_eq!(raw.sec, 99);
    assert!(crate::parse_http_date(std::str::from_utf8(with_second_99).unwrap()).is_err());

    let with_day_00 = b"Sun, 00 Nov 1994 08:49:37 GMT";
    let raw = parse_imf_fixdate(with_day_00).unwrap();
    assert_eq!(raw.day, 0);
    assert!(crate::parse_http_date(std::str::from_utf8(with_day_00).unwrap()).is_err());
}
