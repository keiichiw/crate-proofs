#[cfg(creusot)]
use creusot_std::logic::{OrdLogic, PartialOrdLogic};
#[cfg(creusot)]
use creusot_std::prelude::{
    ensures, invariant, logic, proof_assert, requires, snapshot, DeepModel, Int, Seq,
};

use std::cmp;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[cfg(creusot)]
use crate::stdlib_specs::{
    append_sink, ascii, ascii_content, ascii_trim_relation, formatter_output, time_ns,
};

use crate::Error;

mod debug;
mod hash;

#[cfg(test)]
mod hash_tests;

mod asctime;
use asctime::parse_asctime;
mod rfc850;
use rfc850::parse_rfc850_date;

/// HTTP timestamp type.
///
/// Parse using `FromStr` impl.
/// Format using the `Display` trait.
/// Convert timestamp into/from `SytemTime` to use.
/// Supports comparsion and sorting.
#[derive(Copy)]
pub struct HttpDate {
    /// 0...59
    sec: u8,
    /// 0...59
    min: u8,
    /// 0...23
    hour: u8,
    /// 1...31
    day: u8,
    /// 1...12
    mon: u8,
    /// 1970...9999
    year: u16,
    /// 1...7
    wday: u8,
}

// Raw parser outputs may contain invalid calendar fields. Only the validated
// public type carries the calendar invariant.
#[derive(Copy, Debug)]
pub(crate) struct RawDate {
    sec: u8,
    min: u8,
    hour: u8,
    day: u8,
    mon: u8,
    year: u16,
    wday: u8,
}

impl Clone for HttpDate {
    #[cfg_attr(creusot, ensures(result == *self))]
    fn clone(&self) -> Self {
        *self
    }
}

impl Clone for RawDate {
    #[cfg_attr(creusot, ensures(result == *self))]
    fn clone(&self) -> Self {
        *self
    }
}

#[cfg(creusot)]
impl creusot_std::invariant::Invariant for HttpDate {
    #[logic(open(self))]
    fn invariant(self) -> bool {
        valid_calendar(self.raw_model())
    }
}

impl HttpDate {
    #[cfg(creusot)]
    #[logic(open(self), inline)]
    pub(crate) fn raw_model(self) -> RawDate {
        RawDate {
            sec: self.sec,
            min: self.min,
            hour: self.hour,
            day: self.day,
            mon: self.mon,
            year: self.year,
            wday: self.wday,
        }
    }

    #[cfg_attr(creusot, ensures(result == self.raw_model()))]
    fn as_raw(&self) -> RawDate {
        RawDate {
            sec: self.sec,
            min: self.min,
            hour: self.hour,
            day: self.day,
            mon: self.mon,
            year: self.year,
            wday: self.wday,
        }
    }

    #[cfg_attr(creusot, requires(valid_calendar(d)))]
    #[cfg_attr(creusot, ensures(result.raw_model() == d))]
    fn from_raw(d: RawDate) -> Self {
        Self {
            sec: d.sec,
            min: d.min,
            hour: d.hour,
            day: d.day,
            mon: d.mon,
            year: d.year,
            wday: d.wday,
        }
    }

    #[cfg_attr(creusot, ensures(exists<bytes: Seq<u8>>
        imf_encoding(bytes, self.raw_model())
        && ascii_content(result@, bytes)))]
    pub(crate) fn imf_string(&self) -> String {
        let buf = imf_bytes(&self.as_raw());
        String::from(std::str::from_utf8(&buf).unwrap())
    }
}

#[cfg(creusot)]
impl DeepModel for HttpDate {
    type DeepModelTy = Int;
    #[logic(open(self))]
    fn deep_model(self) -> Int {
        unix_seconds_model(self.raw_model())
    }
}

impl Eq for HttpDate {}

impl PartialEq for HttpDate {
    #[cfg_attr(creusot, ensures(result == (self.deep_model() == other.deep_model())))]
    fn eq(&self, other: &Self) -> bool {
        #[cfg(creusot)]
        {
            let a = self.as_raw();
            let b = other.as_raw();
            if to_unix_seconds(a) == to_unix_seconds(b) {
                valid_datetime_injective(a, b);
            }
        }
        self.sec == other.sec
            && self.min == other.min
            && self.hour == other.hour
            && self.day == other.day
            && self.mon == other.mon
            && self.year == other.year
            && self.wday == other.wday
    }
}

impl From<SystemTime> for HttpDate {
    #[cfg_attr(creusot, requires(0 <= time_ns(v) && time_ns(v) < 253402300800000000000))]
    #[cfg_attr(creusot, ensures(valid_calendar(result.raw_model())))]
    #[cfg_attr(creusot, ensures(unix_seconds_model(result.raw_model()) == time_ns(v) / 1000000000))]
    fn from(v: SystemTime) -> HttpDate {
        let dur = v
            .duration_since(UNIX_EPOCH)
            .expect("all times should be after the epoch");
        let secs_since_epoch = dur.as_secs();

        if secs_since_epoch >= 253402300800 {
            // year 9999
            panic!("date must be before year 9999");
        }

        HttpDate::from_raw(from_unix_seconds(secs_since_epoch))
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn march_prefix(index: Int) -> Int {
    if index == 0 {
        0
    } else if index == 1 {
        31
    } else if index == 2 {
        61
    } else if index == 3 {
        92
    } else if index == 4 {
        122
    } else if index == 5 {
        153
    } else if index == 6 {
        184
    } else if index == 7 {
        214
    } else if index == 8 {
        245
    } else if index == 9 {
        275
    } else if index == 10 {
        306
    } else if index == 11 {
        337
    } else {
        366
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn january_offset(month: Int) -> Int {
    if month == 1 {
        0
    } else if month == 2 {
        31
    } else if month == 3 {
        59
    } else if month == 4 {
        90
    } else if month == 5 {
        120
    } else if month == 6 {
        151
    } else if month == 7 {
        181
    } else if month == 8 {
        212
    } else if month == 9 {
        243
    } else if month == 10 {
        273
    } else if month == 11 {
        304
    } else {
        334
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn january_start(year: Int) -> Int {
    (year - 1970) * 365 + (year - 1969) / 4 - (year - 1901) / 100 + (year - 1601) / 400
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn leap_adjustment(year: Int) -> Int {
    if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
        1
    } else {
        0
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn march_start(year: Int) -> Int {
    (year - 1970) * 365 + 59 + year / 4 - year / 100 + year / 400 - 477
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn month_length(year: Int, month: Int) -> Int {
    if month == 2 {
        28 + leap_adjustment(year)
    } else if month == 4 || month == 6 || month == 9 || month == 11 {
        30
    } else {
        31
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(crate) fn gregorian_day(d: RawDate) -> Int {
    pearlite! {
        january_start(d.year@)
        + january_offset(d.mon@) + d.day@ - 1
        + if d.mon@ > 2 { leap_adjustment(d.year@) } else { 0 }
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(crate) fn valid_calendar(d: RawDate) -> bool {
    pearlite! {
        d.sec@ < 60 && d.min@ < 60 && d.hour@ < 24
        && 1970 <= d.year@ && d.year@ <= 9999 && 1 <= d.mon@ && d.mon@ <= 12
        && 1 <= d.day@ && d.day@ <= month_length(d.year@, d.mon@)
        && d.wday@ == (gregorian_day(d) + 3) % 7 + 1
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(crate) fn unix_seconds_model(d: RawDate) -> Int {
    pearlite! { gregorian_day(d) * 86400 + d.hour@ * 3600 + d.min@ * 60 + d.sec@ }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(crate) fn parsed_text(s: Seq<char>, d: RawDate) -> bool {
    pearlite! {
        ascii(s) && exists<trimmed: Seq<char>, bytes: Seq<u8>>
        ascii_trim_relation(s, trimmed) && ascii_content(trimmed, bytes)
        && (imf_encoding(bytes, d) || rfc850::rfc850_encoding(bytes, d)
            || asctime::asctime_encoding(bytes, d))
    }
}

// Same range checks and whole-second roundtrip as the original validator.
// Comparing fields directly keeps structural equality out of the proof boundary.
#[cfg_attr(creusot, ensures(result == valid_calendar(*d)))]
fn is_valid_date(d: &RawDate) -> bool {
    if !(d.sec < 60
        && d.min < 60
        && d.hour < 24
        && d.day > 0
        && d.day < 32
        && d.mon > 0
        && d.mon <= 12
        && d.year >= 1970
        && d.year <= 9999)
    {
        return false;
    }
    let canonical = from_unix_seconds(to_unix_seconds(*d));
    #[cfg(creusot)]
    proof_assert! { gregorian_day(canonical) == gregorian_day(*d) };
    #[cfg(creusot)]
    proof_assert! { d.day@ <= month_length(d.year@, d.mon@) ==>
    canonical.year == d.year };
    #[cfg(creusot)]
    proof_assert! { d.day@ <= month_length(d.year@, d.mon@) ==>
    canonical.mon == d.mon };
    #[cfg(creusot)]
    proof_assert! { d.day@ <= month_length(d.year@, d.mon@) ==>
    canonical.day == d.day };
    canonical.sec == d.sec
        && canonical.min == d.min
        && canonical.hour == d.hour
        && canonical.day == d.day
        && canonical.mon == d.mon
        && canonical.year == d.year
        && canonical.wday == d.wday
}

// Shared numerical core: native SystemTime handling stays in the wrapper.
#[cfg_attr(creusot, requires(secs_since_epoch@ < 253402300800))]
#[cfg_attr(creusot, ensures(result.sec@ < 60 && result.min@ < 60 && result.hour@ < 24
    && 1 <= result.day@ && result.day@ <= 31 && 1 <= result.mon@ && result.mon@ <= 12
    && 1970 <= result.year@ && result.year@ <= 9999 && 1 <= result.wday@ && result.wday@ <= 7))]
#[cfg_attr(creusot, ensures(gregorian_day(result) == secs_since_epoch@ / 86400))]
#[cfg_attr(creusot, ensures(result.sec@ + result.min@ * 60 + result.hour@ * 3600 == secs_since_epoch@ % 86400))]
#[cfg_attr(creusot, ensures(result.day@ <= month_length(result.year@, result.mon@)))]
#[cfg_attr(creusot, ensures(result.wday@ == (secs_since_epoch@ / 86400 + 3) % 7 + 1))]
fn from_unix_seconds(secs_since_epoch: u64) -> RawDate {
    /* 2000-03-01 (mod 400 year, immediately after feb29 */
    const LEAPOCH: i64 = 11017;
    const DAYS_PER_400Y: i64 = 365 * 400 + 97;
    const DAYS_PER_100Y: i64 = 365 * 100 + 24;
    const DAYS_PER_4Y: i64 = 365 * 4 + 1;

    let days = (secs_since_epoch / 86400) as i64 - LEAPOCH;
    let secs_of_day = secs_since_epoch % 86400;
    #[cfg(creusot)]
    proof_assert! { secs_of_day@ % 60 == (secs_of_day@ % 3600) % 60 };
    #[cfg(creusot)]
    proof_assert! { secs_of_day@ % 60 + (secs_of_day@ % 3600) / 60 * 60
    + secs_of_day@ / 3600 * 3600 == secs_of_day@ };
    #[cfg(creusot)]
    proof_assert! { -11017 <= days@ && days@ <= 2921879 };

    let mut qc_cycles = days / DAYS_PER_400Y;
    let mut remdays = days % DAYS_PER_400Y;

    if remdays < 0 {
        remdays += DAYS_PER_400Y;
        qc_cycles -= 1;
    }

    #[cfg(creusot)]
    proof_assert! { -1 <= qc_cycles@ && qc_cycles@ <= 19 && 0 <= remdays@ && remdays@ <= 146096
    && days@ == 146097 * qc_cycles@ + remdays@
    && (qc_cycles@ == -1 ==> remdays@ >= 135080) };
    let mut c_cycles = remdays / DAYS_PER_100Y;
    if c_cycles == 4 {
        c_cycles -= 1;
    }
    remdays -= c_cycles * DAYS_PER_100Y;

    #[cfg(creusot)]
    proof_assert! { 0 <= c_cycles@ && c_cycles@ <= 3 && 0 <= remdays@ && remdays@ <= 36524
    && days@ == 146097 * qc_cycles@ + 36524 * c_cycles@ + remdays@
    && (qc_cycles@ == -1 ==> c_cycles@ == 3 && remdays@ >= 25508)
    && (c_cycles@ < 3 ==> remdays@ < 36524) };
    let mut q_cycles = remdays / DAYS_PER_4Y;
    if q_cycles == 25 {
        q_cycles -= 1;
    }
    remdays -= q_cycles * DAYS_PER_4Y;

    #[cfg(creusot)]
    proof_assert! { 0 <= q_cycles@ && q_cycles@ <= 24 && 0 <= remdays@ && remdays@ <= 1460
    && days@ == 146097 * qc_cycles@ + 36524 * c_cycles@ + 1461 * q_cycles@ + remdays@
    && (qc_cycles@ == -1 ==> q_cycles@ >= 17)
    && (qc_cycles@ == -1 && q_cycles@ == 17 ==> remdays@ >= 671)
    && (c_cycles@ < 3 && q_cycles@ == 24 ==> remdays@ < 1460) };
    let mut remyears = remdays / 365;
    if remyears == 4 {
        remyears -= 1;
    }
    remdays -= remyears * 365;

    #[cfg(creusot)]
    proof_assert! { 0 <= remyears@ && remyears@ <= 3 && 0 <= remdays@ && remdays@ <= 365
    && days@ == 146097 * qc_cycles@ + 36524 * c_cycles@ + 1461 * q_cycles@ + 365 * remyears@ + remdays@
    && (qc_cycles@ == -1 && q_cycles@ == 17 ==> remyears@ >= 1)
    && (remdays@ == 365 ==> remyears@ == 3 && (q_cycles@ < 24 || c_cycles@ == 3)) };
    let mut year = 2000 + remyears + 4 * q_cycles + 100 * c_cycles + 400 * qc_cycles;

    #[cfg(creusot)]
    proof_assert! { 1969 <= year@ && year@ <= 9999
    && (year@ == 1969 ==> remdays@ >= 306) && (year@ == 9999 ==> remdays@ <= 305) };
    #[cfg(creusot)]
    proof_assert! { year@ / 4 == 500 + 100 * qc_cycles@ + 25 * c_cycles@ + q_cycles@
    && year@ % 4 == remyears@ };
    #[cfg(creusot)]
    proof_assert! { year@ / 100 == 20 + 4 * qc_cycles@ + c_cycles@
    && year@ % 100 == 4 * q_cycles@ + remyears@ };
    #[cfg(creusot)]
    proof_assert! { year@ / 400 == 5 + qc_cycles@
    && year@ % 400 == 100 * c_cycles@ + 4 * q_cycles@ + remyears@ };
    #[cfg(creusot)]
    proof_assert! { remdays@ <= 364 + leap_adjustment(year@ + 1) };
    #[cfg(creusot)]
    proof_assert! { march_start(year@) + remdays@ == days@ + 11017 };
    #[cfg(creusot)]
    proof_assert! { (year@ - 1969) / 4 == year@ / 4 - 492 - if year@ % 4 == 0 { 1 } else { 0 } };
    #[cfg(creusot)]
    proof_assert! { (year@ - 1901) / 100 == year@ / 100 - 19 - if year@ % 100 == 0 { 1 } else { 0 } };
    #[cfg(creusot)]
    proof_assert! { (year@ - 1601) / 400 == year@ / 400 - 4 - if year@ % 400 == 0 { 1 } else { 0 } };
    #[cfg(creusot)]
    proof_assert! { january_start(year@) + 59 + leap_adjustment(year@) == march_start(year@) };
    #[cfg(creusot)]
    proof_assert! { january_start(year@ + 1) == march_start(year@) + 306 };
    #[cfg(creusot)]
    let march_origin = snapshot!(march_start(year@));
    #[cfg(creusot)]
    let doy = snapshot!(remdays@);
    let months = [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
    let mut mon = 0;
    #[cfg_attr(creusot, invariant(mon@ == produced.len() && 0 <= mon@ && mon@ <= 12
        && 0 <= remdays@ && remdays@ + march_prefix(mon@) == *doy))]
    for mon_len in months.iter() {
        #[cfg(creusot)]
        proof_assert! { (*mon_len)@ == march_prefix(mon@ + 1) - march_prefix(mon@)
        && 29 <= (*mon_len)@ && (*mon_len)@ <= 31 };
        mon += 1;
        if remdays < *mon_len {
            break;
        }
        remdays -= *mon_len;
    }
    #[cfg(creusot)]
    proof_assert! { 1 <= mon@ && mon@ <= 12 && remdays@ + march_prefix(mon@ - 1) == *doy
    && remdays@ < march_prefix(mon@) - march_prefix(mon@ - 1) };
    let mday = remdays + 1;
    let mon = if mon + 2 > 12 {
        #[cfg(creusot)]
        proof_assert! { january_offset(mon@ - 10) == march_prefix(mon@ - 1) - 306 };
        year += 1;
        #[cfg(creusot)]
        proof_assert! { january_start(year@) + january_offset(mon@ - 10) + mday@ - 1 == *march_origin + *doy };
        mon - 10
    } else {
        #[cfg(creusot)]
        proof_assert! { january_offset(mon@ + 2) == march_prefix(mon@ - 1) + 59 };
        #[cfg(creusot)]
        proof_assert! { january_start(year@) + january_offset(mon@ + 2) + mday@ - 1
        + leap_adjustment(year@) == *march_origin + *doy };
        mon + 2
    };
    #[cfg(creusot)]
    proof_assert! { january_start(year@) + january_offset(mon@) + mday@ - 1
    + (if mon@ > 2 { leap_adjustment(year@) } else { 0 }) == days@ + 11017 };
    #[cfg(creusot)]
    proof_assert! { mday@ <= month_length(year@, mon@) };

    let mut wday = (3 + days) % 7;
    if wday <= 0 {
        wday += 7
    };
    #[cfg(creusot)]
    proof_assert! { wday@ == (secs_since_epoch@ / 86400 + 3) % 7 + 1 };
    #[cfg(creusot)]
    proof_assert! { 1970 <= year@ && year@ <= 9999 && 1 <= mon@ && mon@ <= 12
    && 1 <= mday@ && mday@ <= 31 && 1 <= wday@ && wday@ <= 7 };
    #[cfg(creusot)]
    proof_assert! { (year as u16)@ == year@ && (mon as u8)@ == mon@
    && (mday as u8)@ == mday@ && (wday as u8)@ == wday@ };
    RawDate {
        sec: (secs_of_day % 60) as u8,
        min: ((secs_of_day % 3600) / 60) as u8,
        hour: (secs_of_day / 3600) as u8,
        day: mday as u8,
        mon: mon as u8,
        year: year as u16,
        wday: wday as u8,
    }
}

impl From<HttpDate> for SystemTime {
    #[cfg_attr(creusot, ensures(time_ns(result) == unix_seconds_model(v.raw_model()) * 1000000000))]
    fn from(v: HttpDate) -> SystemTime {
        UNIX_EPOCH + Duration::from_secs(to_unix_seconds(v.as_raw()))
    }
}

#[cfg_attr(creusot, requires(v.sec@ < 60 && v.min@ < 60 && v.hour@ < 24
    && 1 <= v.day@ && v.day@ <= 31 && 1 <= v.mon@ && v.mon@ <= 12
    && 1970 <= v.year@ && v.year@ <= 9999))]
#[cfg_attr(creusot, ensures(result@ < 253402300800))]
#[cfg_attr(creusot, ensures(result@ == gregorian_day(v) * 86400
    + v.hour@ * 3600 + v.min@ * 60 + v.sec@))]
fn to_unix_seconds(v: RawDate) -> u64 {
    let leap_years =
        ((v.year - 1) - 1968) / 4 - ((v.year - 1) - 1900) / 100 + ((v.year - 1) - 1600) / 400;
    let mut ydays = match v.mon {
        1 => 0,
        2 => 31,
        3 => 59,
        4 => 90,
        5 => 120,
        6 => 151,
        7 => 181,
        8 => 212,
        9 => 243,
        10 => 273,
        11 => 304,
        12 => 334,
        _ => unreachable!(),
    } + v.day as u64
        - 1;
    if is_leap_year(v.year) && v.mon > 2 {
        ydays += 1;
    }
    let days = (v.year as u64 - 1970) * 365 + leap_years as u64 + ydays;
    v.sec as u64 + v.min as u64 * 60 + v.hour as u64 * 3600 + days * 86400
}

impl FromStr for HttpDate {
    type Err = Error;

    #[cfg_attr(creusot, ensures(match result {
        Ok(d) => valid_calendar(d.raw_model()) && parsed_text(s@, d.raw_model()),
        Err(_) => forall<d: RawDate> parsed_text(s@, d) ==> !valid_calendar(d),
    }))]
    fn from_str(s: &str) -> Result<HttpDate, Error> {
        if !s.is_ascii() {
            return Err(Error(()));
        }
        let trimmed = s.trim();
        let x = trimmed.as_bytes();
        #[cfg(creusot)]
        proof_assert! {
            forall<other: Seq<char>, bytes: Seq<u8>>
                ascii_trim_relation(s@, other) && ascii_content(other, bytes) ==> {
                    crate::stdlib_specs::trim_unique(s@, trimmed@, other);
                    crate::stdlib_specs::bytes_unique(trimmed@, x@, bytes);
                    bytes == x@
                }
        };
        match parse_date_bytes(x) {
            Ok(raw) => Ok(HttpDate::from_raw(raw)),
            Err(error) => Err(error),
        }
    }
}

#[cfg_attr(creusot, ensures(match result {
    Ok(d) => valid_calendar(d),
    Err(_) => true,
}))]
#[cfg_attr(creusot, ensures(match result {
    Ok(d) => imf_encoding(s@, d) || rfc850::rfc850_encoding(s@, d)
        || asctime::asctime_encoding(s@, d),
    Err(_) => true,
}))]
#[cfg_attr(creusot, ensures(match result {
    Ok(d) => imf_syntax(s@) ==> imf_encoding(s@, d),
    Err(_) => forall<d: RawDate>
        imf_encoding(s@, d) || rfc850::rfc850_encoding(s@, d)
            || asctime::asctime_encoding(s@, d) ==> !valid_calendar(d),
}))]
fn parse_date_bytes(s: &[u8]) -> Result<RawDate, Error> {
    #[cfg(creusot)]
    proof_assert! {
        asctime::encoding_laws(s@);
        rfc850::encoding_laws(s@);
        true
    };
    let date = match parse_imf_fixdate(s) {
        Ok(date) => date,
        Err(_) => match parse_rfc850_date(s) {
            Ok(date) => date,
            Err(_) => parse_asctime(s)?,
        },
    };
    if !is_valid_date(&date) {
        return Err(Error(()));
    }
    Ok(date)
}

impl Display for HttpDate {
    #[cfg_attr(creusot, ensures(match result {
        Ok(()) => append_sink(*f) ==> exists<chars: Seq<char>, bytes: Seq<u8>>
            imf_encoding(bytes, self.raw_model()) && ascii_content(chars, bytes)
            && formatter_output(^f) == formatter_output(*f).concat(chars),
        Err(_) => true,
    }))]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let buf = imf_bytes(&self.as_raw());
        <Formatter<'_> as std::fmt::Write>::write_str(f, std::str::from_utf8(&buf).unwrap())
    }
}

#[cfg_attr(creusot, requires(d.sec@ < 60 && d.min@ < 60 && d.hour@ < 24
    && 1 <= d.day@ && d.day@ <= 31 && 1 <= d.mon@ && d.mon@ <= 12
    && 1970 <= d.year@ && d.year@ <= 9999 && 1 <= d.wday@ && d.wday@ <= 7))]
#[cfg_attr(creusot, ensures(result@.len() == 29 && forall<i: Int> 0 <= i && i < 29 ==> result@[i]@ < 128))]
#[cfg_attr(creusot, ensures(result[5]@ == 48 + d.day@ / 10 && result[6]@ == 48 + d.day@ % 10
    && result[12]@ == 48 + d.year@ / 1000 && result[13]@ == 48 + (d.year@ / 100) % 10
    && result[14]@ == 48 + (d.year@ / 10) % 10 && result[15]@ == 48 + d.year@ % 10
    && result[17]@ == 48 + d.hour@ / 10 && result[18]@ == 48 + d.hour@ % 10
    && result[20]@ == 48 + d.min@ / 10 && result[21]@ == 48 + d.min@ % 10
    && result[23]@ == 48 + d.sec@ / 10 && result[24]@ == 48 + d.sec@ % 10))]
#[cfg_attr(creusot, ensures(imf_encoding(result@, *d)))]
fn imf_bytes(d: &RawDate) -> [u8; 29] {
    let wday = match d.wday {
        1 => [b'M', b'o', b'n'],
        2 => [b'T', b'u', b'e'],
        3 => [b'W', b'e', b'd'],
        4 => [b'T', b'h', b'u'],
        5 => [b'F', b'r', b'i'],
        6 => [b'S', b'a', b't'],
        7 => [b'S', b'u', b'n'],
        _ => unreachable!(),
    };

    let mon = match d.mon {
        1 => [b'J', b'a', b'n'],
        2 => [b'F', b'e', b'b'],
        3 => [b'M', b'a', b'r'],
        4 => [b'A', b'p', b'r'],
        5 => [b'M', b'a', b'y'],
        6 => [b'J', b'u', b'n'],
        7 => [b'J', b'u', b'l'],
        8 => [b'A', b'u', b'g'],
        9 => [b'S', b'e', b'p'],
        10 => [b'O', b'c', b't'],
        11 => [b'N', b'o', b'v'],
        12 => [b'D', b'e', b'c'],
        _ => unreachable!(),
    };

    let mut buf: [u8; 29] = [
        b' ', b' ', b' ', b',', b' ', b'0', b'0', b' ', b' ', b' ', b' ', b' ', b'0', b'0', b'0',
        b'0', b' ', b'0', b'0', b':', b'0', b'0', b':', b'0', b'0', b' ', b'G', b'M', b'T',
    ];
    buf[0] = wday[0];
    buf[1] = wday[1];
    buf[2] = wday[2];
    buf[5] = b'0' + (d.day / 10);
    buf[6] = b'0' + (d.day % 10);
    buf[8] = mon[0];
    buf[9] = mon[1];
    buf[10] = mon[2];
    buf[12] = b'0' + (d.year / 1000) as u8;
    buf[13] = b'0' + (d.year / 100 % 10) as u8;
    buf[14] = b'0' + (d.year / 10 % 10) as u8;
    buf[15] = b'0' + (d.year % 10) as u8;
    buf[17] = b'0' + (d.hour / 10);
    buf[18] = b'0' + (d.hour % 10);
    buf[20] = b'0' + (d.min / 10);
    buf[21] = b'0' + (d.min % 10);
    buf[23] = b'0' + (d.sec / 10);
    buf[24] = b'0' + (d.sec % 10);
    buf
}

impl Ord for HttpDate {
    #[cfg_attr(creusot, ensures(result == self.deep_model().cmp_log(other.deep_model())))]
    fn cmp(&self, other: &HttpDate) -> cmp::Ordering {
        to_unix_seconds(self.as_raw()).cmp(&to_unix_seconds(other.as_raw()))
    }
}

impl PartialOrd for HttpDate {
    #[cfg_attr(creusot, ensures(result == self.deep_model().partial_cmp_log(other.deep_model())))]
    fn partial_cmp(&self, other: &HttpDate) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg_attr(creusot, ensures(match result {
    Ok(v) => 48 <= x@ && x@ <= 57 && v@ == x@ - 48 && v@ < 10,
    Err(_) => x@ < 48 || 57 < x@
}))]
fn toint_1(x: u8) -> Result<u8, Error> {
    let result = x.wrapping_sub(b'0');
    if result < 10 {
        Ok(result)
    } else {
        Err(Error(()))
    }
}

#[cfg_attr(creusot, requires(s@.len() >= 2))]
#[cfg_attr(creusot, ensures(match result {
    Ok(v) => 48 <= s[0]@ && s[0]@ <= 57 && 48 <= s[1]@ && s[1]@ <= 57
        && v@ == (s[0]@ - 48) * 10 + s[1]@ - 48 && v@ < 100,
    Err(_) => s[0]@ < 48 || 57 < s[0]@ || s[1]@ < 48 || 57 < s[1]@
}))]
fn toint_2(s: &[u8]) -> Result<u8, Error> {
    let high = s[0].wrapping_sub(b'0');
    let low = s[1].wrapping_sub(b'0');

    if high < 10 && low < 10 {
        Ok(high * 10 + low)
    } else {
        Err(Error(()))
    }
}

#[allow(clippy::many_single_char_names)]
#[cfg_attr(creusot, requires(s@.len() >= 4))]
#[cfg_attr(creusot, ensures(match result {
    Ok(v) => 48 <= s[0]@ && s[0]@ <= 57 && 48 <= s[1]@ && s[1]@ <= 57
        && 48 <= s[2]@ && s[2]@ <= 57 && 48 <= s[3]@ && s[3]@ <= 57
        && v@ == (s[0]@ - 48) * 1000 + (s[1]@ - 48) * 100
            + (s[2]@ - 48) * 10 + s[3]@ - 48 && v@ < 10000,
    Err(_) => s[0]@ < 48 || 57 < s[0]@ || s[1]@ < 48 || 57 < s[1]@
        || s[2]@ < 48 || 57 < s[2]@ || s[3]@ < 48 || 57 < s[3]@
}))]
fn toint_4(s: &[u8]) -> Result<u16, Error> {
    let a = u16::from(s[0].wrapping_sub(b'0'));
    let b = u16::from(s[1].wrapping_sub(b'0'));
    let c = u16::from(s[2].wrapping_sub(b'0'));
    let d = u16::from(s[3].wrapping_sub(b'0'));

    if a < 10 && b < 10 && c < 10 && d < 10 {
        Ok(a * 1000 + b * 100 + c * 10 + d)
    } else {
        Err(Error(()))
    }
}

// Logical grammar for the raw IMF parser; not a calendar-validity predicate.
#[cfg(creusot)]
#[logic(open(self), inline)]
fn imf_month(s: Seq<u8>) -> Int {
    if s[7] != 32u8 || s[11] != 32u8 {
        0
    } else {
        if s[8] == 74u8 && s[9] == 97u8 && s[10] == 110u8 {
            1
        } else if s[8] == 70u8 && s[9] == 101u8 && s[10] == 98u8 {
            2
        } else if s[8] == 77u8 && s[9] == 97u8 && s[10] == 114u8 {
            3
        } else if s[8] == 65u8 && s[9] == 112u8 && s[10] == 114u8 {
            4
        } else if s[8] == 77u8 && s[9] == 97u8 && s[10] == 121u8 {
            5
        } else if s[8] == 74u8 && s[9] == 117u8 && s[10] == 110u8 {
            6
        } else if s[8] == 74u8 && s[9] == 117u8 && s[10] == 108u8 {
            7
        } else if s[8] == 65u8 && s[9] == 117u8 && s[10] == 103u8 {
            8
        } else if s[8] == 83u8 && s[9] == 101u8 && s[10] == 112u8 {
            9
        } else if s[8] == 79u8 && s[9] == 99u8 && s[10] == 116u8 {
            10
        } else if s[8] == 78u8 && s[9] == 111u8 && s[10] == 118u8 {
            11
        } else if s[8] == 68u8 && s[9] == 101u8 && s[10] == 99u8 {
            12
        } else {
            0
        }
    }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn imf_weekday(s: Seq<u8>) -> Int {
    if s[3] != 44u8 || s[4] != 32u8 {
        0
    } else {
        if s[0] == 77u8 && s[1] == 111u8 && s[2] == 110u8 {
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
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn imf_digit(b: u8) -> bool {
    pearlite! { 48 <= b@ && b@ <= 57 }
}

#[cfg(creusot)]
#[logic(open(self), inline)]
fn imf_syntax(s: Seq<u8>) -> bool {
    s.len() == 29
        && imf_month(s) > 0
        && imf_weekday(s) > 0
        && s[16] == 32u8
        && s[19] == 58u8
        && s[22] == 58u8
        && s[25] == 32u8
        && s[26] == 71u8
        && s[27] == 77u8
        && s[28] == 84u8
        && imf_digit(s[5])
        && imf_digit(s[6])
        && imf_digit(s[12])
        && imf_digit(s[13])
        && imf_digit(s[14])
        && imf_digit(s[15])
        && imf_digit(s[17])
        && imf_digit(s[18])
        && imf_digit(s[20])
        && imf_digit(s[21])
        && imf_digit(s[23])
        && imf_digit(s[24])
}

#[cfg(creusot)]
#[logic(open(self), inline)]
pub(crate) fn imf_encoding(s: Seq<u8>, d: RawDate) -> bool {
    pearlite! {
    imf_syntax(s) && imf_month(s) == d.mon@ && imf_weekday(s) == d.wday@
    && (s[5]@ - 48) * 10 + s[6]@ - 48 == d.day@
    && (s[12]@ - 48) * 1000 + (s[13]@ - 48) * 100 + (s[14]@ - 48) * 10 + s[15]@ - 48 == d.year@
    && (s[17]@ - 48) * 10 + s[18]@ - 48 == d.hour@
    && (s[20]@ - 48) * 10 + s[21]@ - 48 == d.min@
    && (s[23]@ - 48) * 10 + s[24]@ - 48 == d.sec@
    }
}

// This parser recognizes syntax; calendar validity is checked by FromStr.
// The first milestone proves totality and successful field bounds, not validity.
#[cfg_attr(creusot, ensures(match result {
    Ok(d) => imf_encoding(s@, d) && d.sec@ < 100 && d.min@ < 100
        && d.hour@ < 100 && d.day@ < 100 && 1 <= d.mon@ && d.mon@ <= 12
        && d.year@ < 10000 && 1 <= d.wday@ && d.wday@ <= 7,
    Err(_) => !imf_syntax(s@)
}))]
fn parse_imf_fixdate(s: &[u8]) -> Result<RawDate, Error> {
    // Example: `Sun, 06 Nov 1994 08:49:37 GMT`
    if s.len() != 29
        || s[25] != b' '
        || s[26] != b'G'
        || s[27] != b'M'
        || s[28] != b'T'
        || s[16] != b' '
        || s[19] != b':'
        || s[22] != b':'
    {
        return Err(Error(()));
    }
    Ok(RawDate {
        sec: toint_2(&s[23..25])?,
        min: toint_2(&s[20..22])?,
        hour: toint_2(&s[17..19])?,
        day: toint_2(&s[5..7])?,
        mon: match (s[7], s[8], s[9], s[10], s[11]) {
            (b' ', b'J', b'a', b'n', b' ') => 1,
            (b' ', b'F', b'e', b'b', b' ') => 2,
            (b' ', b'M', b'a', b'r', b' ') => 3,
            (b' ', b'A', b'p', b'r', b' ') => 4,
            (b' ', b'M', b'a', b'y', b' ') => 5,
            (b' ', b'J', b'u', b'n', b' ') => 6,
            (b' ', b'J', b'u', b'l', b' ') => 7,
            (b' ', b'A', b'u', b'g', b' ') => 8,
            (b' ', b'S', b'e', b'p', b' ') => 9,
            (b' ', b'O', b'c', b't', b' ') => 10,
            (b' ', b'N', b'o', b'v', b' ') => 11,
            (b' ', b'D', b'e', b'c', b' ') => 12,
            _ => return Err(Error(())),
        },
        year: toint_4(&s[12..16])?,
        wday: match (s[0], s[1], s[2], s[3], s[4]) {
            (b'M', b'o', b'n', b',', b' ') => 1,
            (b'T', b'u', b'e', b',', b' ') => 2,
            (b'W', b'e', b'd', b',', b' ') => 3,
            (b'T', b'h', b'u', b',', b' ') => 4,
            (b'F', b'r', b'i', b',', b' ') => 5,
            (b'S', b'a', b't', b',', b' ') => 6,
            (b'S', b'u', b'n', b',', b' ') => 7,
            _ => return Err(Error(())),
        },
    })
}

#[cfg_attr(creusot, ensures(result == (y@ % 4 == 0 && (y@ % 100 != 0 || y@ % 400 == 0))))]
fn is_leap_year(y: u16) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

#[cfg(test)]
#[path = "verification_tests.rs"]
mod verification_tests;

#[cfg(test)]
#[path = "trial_tests.rs"]
mod trial_tests;

// Executable proof composition, excluded from native code.
#[cfg(creusot)]
#[requires(d.sec@ < 60 && d.min@ < 60 && d.hour@ < 24
    && 1 <= d.day@ && d.day@ <= 31 && 1 <= d.mon@ && d.mon@ <= 12
    && 1970 <= d.year@ && d.year@ <= 9999 && 1 <= d.wday@ && d.wday@ <= 7)]
#[ensures(match result {
    Ok(v) => v.sec == d.sec && v.min == d.min && v.hour == d.hour
        && v.day == d.day && v.mon == d.mon && v.year == d.year && v.wday == d.wday,
    Err(_) => false
})]
fn imf_roundtrip(d: RawDate) -> Result<RawDate, Error> {
    let bytes = imf_bytes(&d);
    parse_imf_fixdate(&bytes)
}

#[cfg(creusot)]
#[requires(seconds@ < 253402300800)]
#[ensures(result == seconds)]
fn seconds_roundtrip(seconds: u64) -> u64 {
    to_unix_seconds(from_unix_seconds(seconds))
}

// Canonical civil dates with identical day indices have identical fields.
#[cfg(creusot)]
#[requires(1970 <= a.year@ && a.year@ <= 9999 && 1 <= a.mon@ && a.mon@ <= 12
    && 1 <= a.day@ && a.day@ <= month_length(a.year@, a.mon@))]
#[requires(1970 <= b.year@ && b.year@ <= 9999 && 1 <= b.mon@ && b.mon@ <= 12
    && 1 <= b.day@ && b.day@ <= month_length(b.year@, b.mon@))]
#[requires(gregorian_day(a) == gregorian_day(b))]
#[ensures(a.year == b.year && a.mon == b.mon && a.day == b.day)]
fn civil_day_injective(a: RawDate, b: RawDate) {}

#[cfg(creusot)]
#[requires(d.sec@ < 60 && d.min@ < 60 && d.hour@ < 24
    && 1 <= d.mon@ && d.mon@ <= 12 && 1970 <= d.year@ && d.year@ <= 9999
    && 1 <= d.day@ && d.day@ <= month_length(d.year@, d.mon@)
    && d.wday@ == (gregorian_day(d) + 3) % 7 + 1)]
#[ensures(result.sec == d.sec && result.min == d.min && result.hour == d.hour
    && result.day == d.day && result.mon == d.mon && result.year == d.year && result.wday == d.wday)]
fn calendar_roundtrip(d: RawDate) -> RawDate {
    let seconds = to_unix_seconds(d);
    let result = from_unix_seconds(seconds);
    civil_day_injective(d, result);
    result
}

#[cfg(creusot)]
#[requires(valid_calendar(d))]
#[ensures(match result {
    Ok(v) => v.sec == d.sec && v.min == d.min && v.hour == d.hour
        && v.day == d.day && v.mon == d.mon && v.year == d.year && v.wday == d.wday,
    Err(_) => false,
})]
fn valid_imf_roundtrip(d: RawDate) -> Result<RawDate, Error> {
    parse_date_bytes(&imf_bytes(&d))
}

// Calendar and clock fields are uniquely determined by a supported timestamp.
#[cfg(creusot)]
#[requires(valid_calendar(a) && valid_calendar(b))]
#[requires(unix_seconds_model(a) == unix_seconds_model(b))]
#[ensures(a == b)]
fn valid_datetime_injective(a: RawDate, b: RawDate) {
    proof_assert! { gregorian_day(a) == gregorian_day(b) };
    civil_day_injective(a, b);
    proof_assert! { a.hour == b.hour };
    proof_assert! { a.min == b.min };
    proof_assert! { a.sec == b.sec };
}

// The public adapters preserve whole seconds and truncate subsecond precision.
#[cfg(creusot)]
#[requires(0 <= time_ns(t) && time_ns(t) < 253402300800000000000)]
#[ensures(time_ns(result) == (time_ns(t) / 1000000000) * 1000000000)]
fn system_time_roundtrip(t: SystemTime) -> SystemTime {
    SystemTime::from(HttpDate::from(t))
}
