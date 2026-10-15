use super::{toint_1, toint_2, toint_4, Error, RawDate};

#[cfg(creusot)]
use creusot_std::prelude::{ensures, logic, Int, Seq};

// Logical description of the byte grammar accepted by the original parser.
// Numeric byte values avoid a Creusot 0.13 ICE on byte character literals.
#[cfg(creusot)]
#[logic(open(self), inline)]
fn asctime_digit(b: u8) -> bool {
    pearlite! { 48 <= b@ && b@ <= 57 }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn asctime_weekday(s: Seq<u8>) -> Int {
    if s[3] != 32u8 {
        0
    } else if s[0] == 77u8 && s[1] == 111u8 && s[2] == 110u8 {
        1
    } else if s[0] == 84u8 && s[1] == 117u8 && s[2] == 101u8 {
        2
    } else if s[0] == 87u8 && s[1] == 101u8 && s[2] == 100u8 {
        3
    } else if s[0] == 84u8 && s[1] == 104u8 && s[2] == 117u8 {
        4
    } else if s[0] == 70u8 && s[1] == 114u8 && s[2] == 105u8 {
        5
    } else if s[0] == 83u8 && s[1] == 97u8 && s[2] == 116u8 {
        6
    } else if s[0] == 83u8 && s[1] == 117u8 && s[2] == 110u8 {
        7
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn asctime_month(s: Seq<u8>) -> Int {
    if s[7] != 32u8 {
        0
    } else if s[4] == 74u8 && s[5] == 97u8 && s[6] == 110u8 {
        1
    } else if s[4] == 70u8 && s[5] == 101u8 && s[6] == 98u8 {
        2
    } else if s[4] == 77u8 && s[5] == 97u8 && s[6] == 114u8 {
        3
    } else if s[4] == 65u8 && s[5] == 112u8 && s[6] == 114u8 {
        4
    } else if s[4] == 77u8 && s[5] == 97u8 && s[6] == 121u8 {
        5
    } else if s[4] == 74u8 && s[5] == 117u8 && s[6] == 110u8 {
        6
    } else if s[4] == 74u8 && s[5] == 117u8 && s[6] == 108u8 {
        7
    } else if s[4] == 65u8 && s[5] == 117u8 && s[6] == 103u8 {
        8
    } else if s[4] == 83u8 && s[5] == 101u8 && s[6] == 112u8 {
        9
    } else if s[4] == 79u8 && s[5] == 99u8 && s[6] == 116u8 {
        10
    } else if s[4] == 78u8 && s[5] == 111u8 && s[6] == 118u8 {
        11
    } else if s[4] == 68u8 && s[5] == 101u8 && s[6] == 99u8 {
        12
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn asctime_syntax(s: Seq<u8>) -> bool {
    s.len() == 24
        && asctime_weekday(s) > 0
        && asctime_month(s) > 0
        && s[10] == 32u8
        && s[13] == 58u8
        && s[16] == 58u8
        && s[19] == 32u8
        && (if s[8] == 32u8 {
            asctime_digit(s[9])
        } else {
            asctime_digit(s[8]) && asctime_digit(s[9])
        })
        && asctime_digit(s[11])
        && asctime_digit(s[12])
        && asctime_digit(s[14])
        && asctime_digit(s[15])
        && asctime_digit(s[17])
        && asctime_digit(s[18])
        && asctime_digit(s[20])
        && asctime_digit(s[21])
        && asctime_digit(s[22])
        && asctime_digit(s[23])
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(super) fn asctime_encoding(s: Seq<u8>, d: RawDate) -> bool {
    pearlite! {
        asctime_syntax(s)
        && asctime_weekday(s) == d.wday@
        && asctime_month(s) == d.mon@
        && (if s[8]@ == 32 { s[9]@ - 48 } else { (s[8]@ - 48) * 10 + s[9]@ - 48 }) == d.day@
        && (s[11]@ - 48) * 10 + s[12]@ - 48 == d.hour@
        && (s[14]@ - 48) * 10 + s[15]@ - 48 == d.min@
        && (s[17]@ - 48) * 10 + s[18]@ - 48 == d.sec@
        && (s[20]@ - 48) * 1000 + (s[21]@ - 48) * 100 + (s[22]@ - 48) * 10 + s[23]@ - 48 == d.year@
    }
}

#[cfg_attr(creusot, ensures(match result {
    Ok(d) => asctime_encoding(s@, d) && d.sec@ < 100 && d.min@ < 100
        && d.hour@ < 100 && d.day@ < 100 && 1 <= d.mon@ && d.mon@ <= 12
        && d.year@ < 10000 && 1 <= d.wday@ && d.wday@ <= 7,
    Err(_) => !asctime_syntax(s@) && forall<d: RawDate> !asctime_encoding(s@, d)
}))]
pub(super) fn parse_asctime(s: &[u8]) -> Result<RawDate, Error> {
    // Keep the upstream parser's field extraction and error behavior. Scalar
    // tuple matches avoid Creusot 0.13's ICE on byte-slice patterns.
    if s.len() != 24 || s[10] != b' ' || s[13] != b':' || s[16] != b':' || s[19] != b' ' {
        return Err(Error(()));
    }
    Ok(RawDate {
        sec: toint_2(&s[17..19])?,
        min: toint_2(&s[14..16])?,
        hour: toint_2(&s[11..13])?,
        day: {
            let x = &s[8..10];
            if x[0] == b' ' {
                toint_1(x[1])
            } else {
                toint_2(x)
            }?
        },
        mon: match (s[4], s[5], s[6], s[7]) {
            (b'J', b'a', b'n', b' ') => 1,
            (b'F', b'e', b'b', b' ') => 2,
            (b'M', b'a', b'r', b' ') => 3,
            (b'A', b'p', b'r', b' ') => 4,
            (b'M', b'a', b'y', b' ') => 5,
            (b'J', b'u', b'n', b' ') => 6,
            (b'J', b'u', b'l', b' ') => 7,
            (b'A', b'u', b'g', b' ') => 8,
            (b'S', b'e', b'p', b' ') => 9,
            (b'O', b'c', b't', b' ') => 10,
            (b'N', b'o', b'v', b' ') => 11,
            (b'D', b'e', b'c', b' ') => 12,
            _ => return Err(Error(())),
        },
        year: toint_4(&s[20..24])?,
        wday: match (s[0], s[1], s[2], s[3]) {
            (b'M', b'o', b'n', b' ') => 1,
            (b'T', b'u', b'e', b' ') => 2,
            (b'W', b'e', b'd', b' ') => 3,
            (b'T', b'h', b'u', b' ') => 4,
            (b'F', b'r', b'i', b' ') => 5,
            (b'S', b'a', b't', b' ') => 6,
            (b'S', b'u', b'n', b' ') => 7,
            _ => return Err(Error(())),
        },
    })
}

#[cfg(all(test, not(creusot)))]
#[path = "asctime_tests.rs"]
mod tests;

// Verified interface facts for callers outside this grammar module.
#[cfg(creusot)]
#[logic(opaque)]
#[ensures(forall<d: RawDate> asctime_encoding(s, d) ==> s.len() == 24)]
#[ensures(forall<a: RawDate, b: RawDate>
    asctime_encoding(s, a) && asctime_encoding(s, b) ==> a == b)]
pub(super) fn encoding_laws(s: Seq<u8>) {}
