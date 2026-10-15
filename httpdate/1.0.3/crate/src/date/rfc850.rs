use super::{toint_2, Error, RawDate};

#[cfg(creusot)]
use creusot_std::prelude::{ensures, logic, proof_assert, requires, snapshot, Int, Seq};

#[cfg(creusot)]
#[logic(open(self))]
fn rfc850_weekday(s: Seq<u8>) -> Int {
    if s.len() >= 8
        && s[0] == 77u8
        && s[1] == 111u8
        && s[2] == 110u8
        && s[3] == 100u8
        && s[4] == 97u8
        && s[5] == 121u8
        && s[6] == 44u8
        && s[7] == 32u8
    {
        1
    } else if s.len() >= 9
        && s[0] == 84u8
        && s[1] == 117u8
        && s[2] == 101u8
        && s[3] == 115u8
        && s[4] == 100u8
        && s[5] == 97u8
        && s[6] == 121u8
        && s[7] == 44u8
        && s[8] == 32u8
    {
        2
    } else if s.len() >= 11
        && s[0] == 87u8
        && s[1] == 101u8
        && s[2] == 100u8
        && s[3] == 110u8
        && s[4] == 101u8
        && s[5] == 115u8
        && s[6] == 100u8
        && s[7] == 97u8
        && s[8] == 121u8
        && s[9] == 44u8
        && s[10] == 32u8
    {
        3
    } else if s.len() >= 10
        && s[0] == 84u8
        && s[1] == 104u8
        && s[2] == 117u8
        && s[3] == 114u8
        && s[4] == 115u8
        && s[5] == 100u8
        && s[6] == 97u8
        && s[7] == 121u8
        && s[8] == 44u8
        && s[9] == 32u8
    {
        4
    } else if s.len() >= 8
        && s[0] == 70u8
        && s[1] == 114u8
        && s[2] == 105u8
        && s[3] == 100u8
        && s[4] == 97u8
        && s[5] == 121u8
        && s[6] == 44u8
        && s[7] == 32u8
    {
        5
    } else if s.len() >= 10
        && s[0] == 83u8
        && s[1] == 97u8
        && s[2] == 116u8
        && s[3] == 117u8
        && s[4] == 114u8
        && s[5] == 100u8
        && s[6] == 97u8
        && s[7] == 121u8
        && s[8] == 44u8
        && s[9] == 32u8
    {
        6
    } else if s.len() >= 8
        && s[0] == 83u8
        && s[1] == 117u8
        && s[2] == 110u8
        && s[3] == 100u8
        && s[4] == 97u8
        && s[5] == 121u8
        && s[6] == 44u8
        && s[7] == 32u8
    {
        7
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self))]
fn rfc850_prefix_len(s: Seq<u8>) -> Int {
    if rfc850_weekday(s) == 1 || rfc850_weekday(s) == 5 || rfc850_weekday(s) == 7 {
        8
    } else if rfc850_weekday(s) == 2 {
        9
    } else if rfc850_weekday(s) == 3 {
        11
    } else if rfc850_weekday(s) == 4 || rfc850_weekday(s) == 6 {
        10
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self))]
fn rfc850_suffix(s: Seq<u8>) -> Seq<u8> {
    s.subsequence(rfc850_prefix_len(s), s.len())
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn rfc850_digit(b: u8) -> bool {
    pearlite! { 48 <= b@ && b@ <= 57 }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn rfc850_digit_at(s: Seq<u8>, index: Int) -> bool {
    if index < 0 || index >= s.len() {
        false
    } else {
        rfc850_digit(s[index])
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn rfc850_two_digits(s: Seq<u8>, index: Int) -> Int {
    if index < 0 || index + 1 >= s.len() {
        0
    } else {
        pearlite! { (s[index]@ - 48) * 10 + s[index + 1]@ - 48 }
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn rfc850_month(s: Seq<u8>) -> Int {
    if s.len() != 22 || s[2] != 45u8 || s[6] != 45u8 {
        0
    } else if s[3] == 74u8 && s[4] == 97u8 && s[5] == 110u8 {
        1
    } else if s[3] == 70u8 && s[4] == 101u8 && s[5] == 98u8 {
        2
    } else if s[3] == 77u8 && s[4] == 97u8 && s[5] == 114u8 {
        3
    } else if s[3] == 65u8 && s[4] == 112u8 && s[5] == 114u8 {
        4
    } else if s[3] == 77u8 && s[4] == 97u8 && s[5] == 121u8 {
        5
    } else if s[3] == 74u8 && s[4] == 117u8 && s[5] == 110u8 {
        6
    } else if s[3] == 74u8 && s[4] == 117u8 && s[5] == 108u8 {
        7
    } else if s[3] == 65u8 && s[4] == 117u8 && s[5] == 103u8 {
        8
    } else if s[3] == 83u8 && s[4] == 101u8 && s[5] == 112u8 {
        9
    } else if s[3] == 79u8 && s[4] == 99u8 && s[5] == 116u8 {
        10
    } else if s[3] == 78u8 && s[4] == 111u8 && s[5] == 118u8 {
        11
    } else if s[3] == 68u8 && s[4] == 101u8 && s[5] == 99u8 {
        12
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn rfc850_syntax(s: Seq<u8>) -> bool {
    let suffix = rfc850_suffix(s);
    s.len() >= 23
        && rfc850_weekday(s) > 0
        && suffix.len() == 22
        && rfc850_month(suffix) > 0
        && rfc850_digit_at(suffix, 0)
        && rfc850_digit_at(suffix, 1)
        && rfc850_digit_at(suffix, 7)
        && rfc850_digit_at(suffix, 8)
        && rfc850_digit_at(suffix, 10)
        && rfc850_digit_at(suffix, 11)
        && rfc850_digit_at(suffix, 13)
        && rfc850_digit_at(suffix, 14)
        && rfc850_digit_at(suffix, 16)
        && rfc850_digit_at(suffix, 17)
        && suffix[12] == 58u8
        && suffix[15] == 58u8
        && suffix[18] == 32u8
        && suffix[19] == 71u8
        && suffix[20] == 77u8
        && suffix[21] == 84u8
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(super) fn rfc850_encoding(s: Seq<u8>, d: RawDate) -> bool {
    let suffix = rfc850_suffix(s);
    pearlite! {
        rfc850_syntax(s)
        && rfc850_weekday(s) == d.wday@
        && rfc850_month(suffix) == d.mon@
        && rfc850_two_digits(suffix, 0) == d.day@
        && (if rfc850_two_digits(suffix, 7) < 70 {
            rfc850_two_digits(suffix, 7) + 2000
        } else {
            rfc850_two_digits(suffix, 7) + 1900
        }) == d.year@
        && rfc850_two_digits(suffix, 10) == d.hour@
        && rfc850_two_digits(suffix, 13) == d.min@
        && rfc850_two_digits(suffix, 16) == d.sec@
    }
}

// Example: `Sunday, 06-Nov-94 08:49:37 GMT`
#[cfg_attr(creusot, ensures(match result {
    Ok(d) => rfc850_encoding(s@, d)
        && d.sec@ < 100 && d.min@ < 100 && d.hour@ < 100 && d.day@ < 100
        && 1970 <= d.year@ && d.year@ <= 2069 && 1 <= d.mon@ && d.mon@ <= 12
        && 1 <= d.wday@ && d.wday@ <= 7,
    Err(_) => !rfc850_syntax(s@) && forall<d: RawDate> !rfc850_encoding(s@, d)
}))]
pub(super) fn parse_rfc850_date(s: &[u8]) -> Result<RawDate, Error> {
    #[cfg(creusot)]
    let original = snapshot!(s@);
    if s.len() < 23 {
        return Err(Error(()));
    }

    #[cfg_attr(creusot, requires(name@.len() <= s@.len() && 1 <= wday@ && wday@ <= 7))]
    #[cfg_attr(creusot, ensures(match result {
        Some((found_wday, suffix)) => found_wday == wday && suffix@ == s@[name@.len()..]
            && s@[0..name@.len()] == name@,
        None => s@[0..name@.len()] != name@
            && !s@[0..name@.len()].ext_eq(name@)
    }))]
    fn wday<'a>(s: &'a [u8], wday: u8, name: &'static [u8]) -> Option<(u8, &'a [u8])> {
        if &s[0..name.len()] == name {
            return Some((wday, &s[name.len()..]));
        }
        None
    }

    let weekday_match = wday(s, 1, &[b'M', b'o', b'n', b'd', b'a', b'y', b',', b' '])
        .or_else(|| {
            wday(
                s,
                2,
                &[b'T', b'u', b'e', b's', b'd', b'a', b'y', b',', b' '],
            )
        })
        .or_else(|| {
            wday(
                s,
                3,
                &[
                    b'W', b'e', b'd', b'n', b'e', b's', b'd', b'a', b'y', b',', b' ',
                ],
            )
        })
        .or_else(|| {
            wday(
                s,
                4,
                &[b'T', b'h', b'u', b'r', b's', b'd', b'a', b'y', b',', b' '],
            )
        })
        .or_else(|| wday(s, 5, &[b'F', b'r', b'i', b'd', b'a', b'y', b',', b' ']))
        .or_else(|| {
            wday(
                s,
                6,
                &[b'S', b'a', b't', b'u', b'r', b'd', b'a', b'y', b',', b' '],
            )
        })
        .or_else(|| wday(s, 7, &[b'S', b'u', b'n', b'd', b'a', b'y', b',', b' ']));
    #[cfg(creusot)]
    proof_assert! { match weekday_match {
        None => rfc850_weekday(*original) == 0,
        Some(_) => true,
    } };
    let (wday, s) = weekday_match.ok_or(Error(()))?;
    #[cfg(creusot)]
    proof_assert! { rfc850_weekday(*original) == wday@ };
    #[cfg(creusot)]
    proof_assert! { s@ == rfc850_suffix(*original) };
    if s.len() != 22
        || s[12] != b':'
        || s[15] != b':'
        || (s[18], s[19], s[20], s[21]) != (b' ', b'G', b'M', b'T')
    {
        return Err(Error(()));
    }
    #[cfg(creusot)]
    proof_assert! {
        rfc850_syntax(*original) ==> 48 <= s[7]@ && s[7]@ <= 57
    };
    #[cfg(creusot)]
    proof_assert! {
        rfc850_syntax(*original) ==> 48 <= s[8]@ && s[8]@ <= 57
    };
    let mut year = u16::from(toint_2(&s[7..9])?);
    if year < 70 {
        year += 2000;
    } else {
        year += 1900;
    }
    let parsed = RawDate {
        sec: toint_2(&s[16..18])?,
        min: toint_2(&s[13..15])?,
        hour: toint_2(&s[10..12])?,
        day: toint_2(&s[0..2])?,
        mon: match (s[2], s[3], s[4], s[5], s[6]) {
            (b'-', b'J', b'a', b'n', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 1 };
                1
            }
            (b'-', b'F', b'e', b'b', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 2 };
                2
            }
            (b'-', b'M', b'a', b'r', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 3 };
                3
            }
            (b'-', b'A', b'p', b'r', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 4 };
                4
            }
            (b'-', b'M', b'a', b'y', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 5 };
                5
            }
            (b'-', b'J', b'u', b'n', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 6 };
                6
            }
            (b'-', b'J', b'u', b'l', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 7 };
                7
            }
            (b'-', b'A', b'u', b'g', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 8 };
                8
            }
            (b'-', b'S', b'e', b'p', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 9 };
                9
            }
            (b'-', b'O', b'c', b't', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 10 };
                10
            }
            (b'-', b'N', b'o', b'v', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 11 };
                11
            }
            (b'-', b'D', b'e', b'c', b'-') => {
                #[cfg(creusot)]
                proof_assert! { rfc850_month(s@) == 12 };
                12
            }
            _ => return Err(Error(())),
        },
        year,
        wday,
    };
    #[cfg(creusot)]
    proof_assert! { rfc850_syntax(*original) };
    #[cfg(creusot)]
    proof_assert! { rfc850_weekday(*original) == parsed.wday@ };
    #[cfg(creusot)]
    proof_assert! { rfc850_month(s@) == parsed.mon@ };
    #[cfg(creusot)]
    proof_assert! { rfc850_two_digits(s@, 0) == parsed.day@ };
    #[cfg(creusot)]
    proof_assert! {
        (if rfc850_two_digits(s@, 7) < 70 {
            rfc850_two_digits(s@, 7) + 2000
        } else {
            rfc850_two_digits(s@, 7) + 1900
        }) == parsed.year@
    };
    #[cfg(creusot)]
    proof_assert! { rfc850_two_digits(s@, 10) == parsed.hour@ };
    #[cfg(creusot)]
    proof_assert! { rfc850_two_digits(s@, 13) == parsed.min@ };
    #[cfg(creusot)]
    proof_assert! { rfc850_two_digits(s@, 16) == parsed.sec@ };
    Ok(parsed)
}

#[cfg(all(test, not(creusot)))]
mod tests {
    use super::parse_rfc850_date;

    #[test]
    fn weekday_prefixes_and_two_digit_year_pivot() {
        let cases: [(&[u8], u8); 7] = [
            (b"Monday, ", 1),
            (b"Tuesday, ", 2),
            (b"Wednesday, ", 3),
            (b"Thursday, ", 4),
            (b"Friday, ", 5),
            (b"Saturday, ", 6),
            (b"Sunday, ", 7),
        ];

        for (prefix, expected_wday) in cases {
            let mut input = prefix.to_vec();
            input.extend_from_slice(b"06-Nov-69 08:49:37 GMT");
            let parsed = parse_rfc850_date(&input).expect("weekday prefix should parse");
            assert_eq!(parsed.wday, expected_wday);
            assert_eq!(parsed.year, 2069);
            assert_eq!(parsed.sec, 37);
            assert_eq!(parsed.min, 49);
            assert_eq!(parsed.hour, 8);
            assert_eq!(parsed.day, 6);
            assert_eq!(parsed.mon, 11);
        }

        let parsed = parse_rfc850_date(b"Sunday, 06-Nov-70 08:49:37 GMT")
            .expect("year 70 should use the 1900 pivot branch");
        assert_eq!(parsed.year, 1970);
    }

    #[test]
    fn year_hour_separator_behavior_matches_upstream() {
        let parsed = parse_rfc850_date(b"Sunday, 06-Nov-94x08:49:37 GMT")
            .expect("the upstream parser does not validate this separator");
        assert_eq!(parsed.wday, 7);
        assert_eq!(parsed.year, 1994);
    }
}

// Verified interface facts for callers outside this grammar module.
#[cfg(creusot)]
#[logic(opaque)]
#[ensures(forall<d: RawDate> rfc850_encoding(s, d) ==> 30 <= s.len() && s.len() <= 33)]
#[ensures(forall<a: RawDate, b: RawDate>
    rfc850_encoding(s, a) && rfc850_encoding(s, b) ==> a == b)]
pub(super) fn encoding_laws(s: Seq<u8>) {}
