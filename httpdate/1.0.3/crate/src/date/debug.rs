//! Checked normal and pretty Debug; standard builders preserve other options.
use super::HttpDate;
use crate::debug_support::*;
#[cfg(creusot)]
use crate::stdlib_specs::*;
#[cfg(creusot)]
use creusot_std::prelude::*;
use std::fmt::{self, Debug, Formatter};

#[cfg(creusot)]
#[logic(open(self), inline)]
fn date_debug_chars(
    sec: u8,
    min: u8,
    hour: u8,
    day: u8,
    mon: u8,
    year: u16,
    wday: u8,
    pretty: bool,
) -> Seq<char> {
    seq!['H', 't', 't', 'p', 'D', 'a', 't', 'e']
        .concat(field_chars(
            pretty,
            true,
            seq!['s', 'e', 'c'],
            decimal_chars(sec.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['m', 'i', 'n'],
            decimal_chars(min.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['h', 'o', 'u', 'r'],
            decimal_chars(hour.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['d', 'a', 'y'],
            decimal_chars(day.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['m', 'o', 'n'],
            decimal_chars(mon.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['y', 'e', 'a', 'r'],
            decimal_chars(year.view()),
        ))
        .concat(field_chars(
            pretty,
            false,
            seq!['w', 'd', 'a', 'y'],
            decimal_chars(wday.view()),
        ))
        .concat(if pretty { seq!['}'] } else { seq![' ', '}'] })
}

impl Debug for HttpDate {
    #[cfg_attr(creusot, ensures(match result {
        Ok(()) => plain_options(debug_options(*f)) && append_sink(*f) ==>
            formatter_output(^f) == formatter_output(*f).concat(date_debug_chars(
                self.sec, self.min, self.hour, self.day, self.mon, self.year, self.wday,
                debug_options(*f).flags == 4u32)),
        Err(_) => true,
    }))]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        #[cfg(creusot)]
        proof_assert! { concat_law(); true };
        let pretty = match debug_mode(f) {
            Some(pretty) => pretty,
            None => {
                return f
                    .debug_struct("HttpDate")
                    .field("sec", &self.sec)
                    .field("min", &self.min)
                    .field("hour", &self.hour)
                    .field("day", &self.day)
                    .field("mon", &self.mon)
                    .field("year", &self.year)
                    .field("wday", &self.wday)
                    .finish()
            }
        };
        #[cfg(creusot)]
        let initial = snapshot!(formatter_output(*f));
        #[cfg(creusot)]
        let sink = snapshot!(append_sink(*f));
        let header = [b'H', b't', b't', b'p', b'D', b'a', b't', b'e'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(header@).ext_eq(seq!['H', 't', 't', 'p', 'D', 'a', 't', 'e']) };
        #[cfg(creusot)]
        let chars0 = snapshot!(seq!['H', 't', 't', 'p', 'D', 'a', 't', 'e']);
        write_ascii(f, &header)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars0) };
        let name1 = [b's', b'e', b'c'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name1@).ext_eq(seq!['s', 'e', 'c']) };
        #[cfg(creusot)]
        let chars1 = snapshot!((*chars0).concat(field_chars(pretty, true, seq!['s', 'e', 'c'], decimal_chars(self.sec@))));
        write_field_u8(f, pretty, true, &name1, self.sec)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars1) };
        let name2 = [b'm', b'i', b'n'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name2@).ext_eq(seq!['m', 'i', 'n']) };
        #[cfg(creusot)]
        let chars2 = snapshot!((*chars1).concat(field_chars(pretty, false, seq!['m', 'i', 'n'], decimal_chars(self.min@))));
        write_field_u8(f, pretty, false, &name2, self.min)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars2) };
        let name3 = [b'h', b'o', b'u', b'r'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name3@).ext_eq(seq!['h', 'o', 'u', 'r']) };
        #[cfg(creusot)]
        let chars3 = snapshot!((*chars2).concat(field_chars(pretty, false, seq!['h', 'o', 'u', 'r'], decimal_chars(self.hour@))));
        write_field_u8(f, pretty, false, &name3, self.hour)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars3) };
        let name4 = [b'd', b'a', b'y'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name4@).ext_eq(seq!['d', 'a', 'y']) };
        #[cfg(creusot)]
        let chars4 = snapshot!((*chars3).concat(field_chars(pretty, false, seq!['d', 'a', 'y'], decimal_chars(self.day@))));
        write_field_u8(f, pretty, false, &name4, self.day)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars4) };
        let name5 = [b'm', b'o', b'n'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name5@).ext_eq(seq!['m', 'o', 'n']) };
        #[cfg(creusot)]
        let chars5 = snapshot!((*chars4).concat(field_chars(pretty, false, seq!['m', 'o', 'n'], decimal_chars(self.mon@))));
        write_field_u8(f, pretty, false, &name5, self.mon)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars5) };
        let name6 = [b'y', b'e', b'a', b'r'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name6@).ext_eq(seq!['y', 'e', 'a', 'r']) };
        #[cfg(creusot)]
        let chars6 = snapshot!((*chars5).concat(field_chars(pretty, false, seq!['y', 'e', 'a', 'r'], decimal_chars(self.year@))));
        write_field_u16(f, pretty, false, &name6, self.year)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars6) };
        let name7 = [b'w', b'd', b'a', b'y'];
        #[cfg(creusot)]
        proof_assert! { ascii_chars(name7@).ext_eq(seq!['w', 'd', 'a', 'y']) };
        #[cfg(creusot)]
        let chars7 = snapshot!((*chars6).concat(field_chars(pretty, false, seq!['w', 'd', 'a', 'y'], decimal_chars(self.wday@))));
        write_field_u8(f, pretty, false, &name7, self.wday)?;
        #[cfg(creusot)]
        proof_assert! { *sink ==> formatter_output(*f) == (*initial).concat(*chars7) };
        if pretty {
            let end = [b'}'];
            #[cfg(creusot)]
            proof_assert! { ascii_chars(end@).ext_eq(seq!['}']) };
            write_ascii(f, &end)
        } else {
            let end = [b' ', b'}'];
            #[cfg(creusot)]
            proof_assert! { ascii_chars(end@).ext_eq(seq![' ', '}']) };
            write_ascii(f, &end)
        }
    }
}
