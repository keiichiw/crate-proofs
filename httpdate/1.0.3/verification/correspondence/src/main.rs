//! Finite native comparisons against unchanged crates.io 1.0.3 Rust sources.
//! These observations are not a proof of semantic equivalence.
#![allow(deprecated)]

use std::collections::hash_map::DefaultHasher;
use std::error::Error as _;
use std::fmt::{self, Debug, Display};
use std::hash::{Hash, Hasher};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const LIMIT: u64 = 253_402_300_800;
const SEED: u64 = 0x6874_7470_6461_7465;

#[derive(Default)]
struct Counts {
    civil_days: u64,
    boundary_instants: u64,
    parser_inputs: u64,
    trait_pairs: u64,
    formatting_observations: u64,
    writer_observations: u64,
    panic_observations: u64,
    error_observations: u64,
}

fn seconds(time: SystemTime) -> u64 {
    time.duration_since(UNIX_EPOCH).unwrap().as_secs()
}

// Compile both crates against the same public trait surface. This is a native
// interface check, independent of the selected formal proof inventory.
fn public_date_surface<D, E>()
where
    D: Copy
        + Clone
        + Debug
        + Display
        + Eq
        + Ord
        + PartialOrd
        + Hash
        + From<SystemTime>
        + Into<SystemTime>
        + std::str::FromStr<Err = E>
        + Send
        + Sync
        + Unpin,
    E: std::error::Error + Send + Sync + 'static,
{
    assert_eq!(std::mem::size_of::<D>(), 8);
}

fn compare_parse(input: &str, counts: &mut Counts) {
    let a = verified::parse_http_date(input);
    let b = released::parse_http_date(input);
    assert_eq!(a.as_ref().ok(), b.as_ref().ok(), "public parse: {input:?}");
    let ad = input.parse::<verified::HttpDate>();
    let bd = input.parse::<released::HttpDate>();
    assert_eq!(ad.as_ref().ok().map(|d| SystemTime::from(*d)), a.ok());
    assert_eq!(bd.as_ref().ok().map(|d| SystemTime::from(*d)), b.ok());
    match (ad, bd) {
        (Ok(x), Ok(y)) => assert_eq!(x.to_string(), y.to_string()),
        (Err(x), Err(y)) => {
            assert_eq!(x.to_string(), y.to_string());
            assert_eq!(format!("{x:?}"), format!("{y:?}"));
        }
        _ => panic!("FromStr outcomes differ: {input:?}"),
    }
    counts.parser_inputs += 1;
}

fn compare_instant(t: SystemTime) {
    let a = verified::HttpDate::from(t);
    let b = released::HttpDate::from(t);
    let af = verified::fmt_http_date(t);
    let bf = released::fmt_http_date(t);
    assert_eq!(af, bf, "format at {t:?}");
    assert_eq!(a.to_string(), bf);
    assert_eq!(b.to_string(), bf);
    let floor = UNIX_EPOCH + Duration::from_secs(seconds(t));
    assert_eq!(SystemTime::from(a), floor);
    assert_eq!(SystemTime::from(b), floor);
    assert_eq!(verified::parse_http_date(&bf).unwrap(), floor);
    assert_eq!(released::parse_http_date(&bf).unwrap(), floor);
    assert_eq!(bf.parse::<verified::HttpDate>().unwrap(), a);
    assert_eq!(bf.parse::<released::HttpDate>().unwrap(), b);
}

#[derive(Debug, PartialEq, Eq)]
enum Write {
    Bytes(Vec<u8>),
    U8(u8),
    U16(u16),
}

#[derive(Default)]
struct TypedHasher(Vec<Write>);
impl Hasher for TypedHasher {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, bytes: &[u8]) {
        self.0.push(Write::Bytes(bytes.to_vec()));
    }
    fn write_u8(&mut self, value: u8) {
        self.0.push(Write::U8(value));
    }
    fn write_u16(&mut self, value: u16) {
        self.0.push(Write::U16(value));
    }
}

fn digest<T: Hash>(value: &T) -> u64 {
    let mut state = DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn compare_traits(s: u64, counts: &mut Counts) {
    let t = UNIX_EPOCH + Duration::from_secs(s);
    let a = verified::HttpDate::from(t);
    let b = released::HttpDate::from(t);
    for other in [s, s.saturating_sub(1), (s + 1).min(LIMIT - 1)] {
        let t2 = UNIX_EPOCH + Duration::from_secs(other);
        let a2 = verified::HttpDate::from(t2);
        let b2 = released::HttpDate::from(t2);
        assert_eq!(a == a2, b == b2);
        assert_eq!(a != a2, b != b2);
        assert_eq!(a.cmp(&a2), b.cmp(&b2));
        assert_eq!(a.partial_cmp(&a2), b.partial_cmp(&b2));
        assert_eq!(a < a2, b < b2);
        assert_eq!(a <= a2, b <= b2);
        assert_eq!(a > a2, b > b2);
        assert_eq!(a >= a2, b >= b2);
        counts.trait_pairs += 1;
    }
    assert_eq!(a.clone(), a);
    assert_eq!(b.clone(), b);
    assert_eq!(digest(&a), digest(&b));
    let mut ah = TypedHasher::default();
    let mut bh = TypedHasher::default();
    a.hash(&mut ah);
    b.hash(&mut bh);
    assert_eq!(ah.0, bh.0);
    let mut ah = TypedHasher::default();
    let mut bh = TypedHasher::default();
    Hash::hash_slice(&[a, a], &mut ah);
    Hash::hash_slice(&[b, b], &mut bh);
    assert_eq!(ah.0, bh.0);
}

#[derive(Debug)]
#[allow(dead_code)]
struct Envelope<T> {
    label: &'static str,
    value: T,
}

fn debug_variants<T: Debug>(value: &T) -> Vec<String> {
    vec![
        format!("{value:?}"),
        format!("{value:#?}"),
        format!("{value:x?}"),
        format!("{value:#x?}"),
        format!("{value:X?}"),
        format!("{value:#X?}"),
        format!("{value:+?}"),
        format!("{value:08?}"),
        format!("{value:10?}"),
        format!("{value:.0?}"),
        format!("{value:.1?}"),
        format!("{value:.2?}"),
        format!("{value:*>8?}"),
        format!("{value:_<8?}"),
        format!("{value:^10?}"),
    ]
}

#[derive(Default, Debug, PartialEq, Eq)]
struct Trace {
    chunks: Vec<String>,
    writes: usize,
    fail_after: usize,
    panic_on_failure: bool,
}
impl fmt::Write for Trace {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.chunks.push(text.to_owned());
        if self.writes == self.fail_after {
            if self.panic_on_failure {
                panic!("controlled writer panic");
            }
            return Err(fmt::Error);
        }
        self.writes += 1;
        Ok(())
    }
}

macro_rules! compare_writer {
    ($fmt:literal, $a:expr, $b:expr, $counts:expr) => {{
        for panic_on_failure in [false, true] {
            for fail_after in 0..64 {
                let mut a = Trace {
                    fail_after,
                    panic_on_failure,
                    ..Trace::default()
                };
                let mut b = Trace {
                    fail_after,
                    panic_on_failure,
                    ..Trace::default()
                };
                let ar = catch_unwind(AssertUnwindSafe(|| {
                    fmt::write(&mut a, format_args!($fmt, $a))
                }));
                let br = catch_unwind(AssertUnwindSafe(|| {
                    fmt::write(&mut b, format_args!($fmt, $b))
                }));
                assert_eq!(ar.is_err(), br.is_err(), "writer panic, format {}", $fmt);
                if let (Ok(ar), Ok(br)) = (ar, br) {
                    assert_eq!(ar.is_err(), br.is_err());
                }
                assert_eq!(
                    a, b,
                    "writer chunks, format {}, fail after {}",
                    $fmt, fail_after
                );
                $counts.writer_observations += 1;
            }
        }
    }};
}

fn compare_formatting<A: Debug + Display, B: Debug + Display>(a: &A, b: &B, counts: &mut Counts) {
    let av = debug_variants(a);
    let bv = debug_variants(b);
    assert_eq!(av, bv);
    counts.formatting_observations += av.len() as u64;
    let ae = Envelope {
        label: "date",
        value: a,
    };
    let be = Envelope {
        label: "date",
        value: b,
    };
    assert_eq!(format!("{ae:?}"), format!("{be:?}"));
    assert_eq!(format!("{ae:#?}"), format!("{be:#?}"));
    assert_eq!(format!("{ae:#10.1?}"), format!("{be:#10.1?}"));
    counts.formatting_observations += 3;
    compare_writer!("{}", a, b, counts);
    compare_writer!("{:?}", a, b, counts);
    compare_writer!("{:#?}", a, b, counts);
    compare_writer!("{:#10.1?}", a, b, counts);
}

fn parser_corpus(counts: &mut Counts) {
    let fixtures = [
        "Sun, 06 Nov 1994 08:49:37 GMT",
        "Sunday, 06-Nov-94 08:49:37 GMT",
        "Sun Nov  6 08:49:37 1994",
        "Wednesday, 06-Nov-69 08:49:37 GMT",
        "Friday, 06-Nov-70 08:49:37 GMT",
        "Tue Feb 29 00:00:00 2000",
        "Thu, 01 Jan 1970 00:00:00 GMT",
        "Fri, 31 Dec 9999 23:59:59 GMT",
    ];
    for fixture in fixtures {
        for i in 0..fixture.len() {
            for byte in 0..=127 {
                let mut bytes = fixture.as_bytes().to_vec();
                bytes[i] = byte;
                compare_parse(std::str::from_utf8(&bytes).unwrap(), counts);
            }
        }
        for end in 0..=fixture.len() {
            compare_parse(&fixture[..end], counts);
        }
        for whitespace in ['\t', '\n', '\u{b}', '\u{c}', '\r', ' '] {
            for trailing in ['\t', '\n', '\u{b}', '\u{c}', '\r', ' '] {
                compare_parse(&format!("{whitespace}{fixture}{trailing}"), counts);
            }
        }
        for extra in ["x", "\0", "\u{85}", "\u{a0}", "é", "\u{65e5}", "😀"] {
            compare_parse(&format!("{extra}{fixture}"), counts);
            compare_parse(&format!("{fixture}{extra}"), counts);
        }
    }
    let months = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    let weekdays = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    for year in [
        0, 1969, 1970, 1971, 1999, 2000, 2004, 2099, 2100, 2399, 2400, 9999,
    ] {
        for month in months {
            for day in 0..=35 {
                for weekday in weekdays {
                    compare_parse(
                        &format!("{weekday}, {day:02} {month} {year:04} 12:34:56 GMT"),
                        counts,
                    );
                }
            }
        }
    }
    for hour in [0, 23, 24, 59, 60, 99] {
        for minute in [0, 59, 60, 99] {
            for second in [0, 59, 60, 99] {
                compare_parse(
                    &format!("Thu, 01 Jan 1970 {hour:02}:{minute:02}:{second:02} GMT"),
                    counts,
                );
            }
        }
    }
    // Every fixed-pivot year with the correct weekday, derived independently by the release formatter.
    let full_weekdays = [
        "Monday",
        "Tuesday",
        "Wednesday",
        "Thursday",
        "Friday",
        "Saturday",
        "Sunday",
    ];
    for year in 0..100 {
        let full_year = if year < 70 { 2000 + year } else { 1900 + year };
        let day = (0..7)
            .map(|i| format!("{}, 06 Nov {full_year} 08:49:37 GMT", weekdays[i]))
            .find_map(|text| released::parse_http_date(&text).ok())
            .unwrap();
        let text = released::fmt_http_date(day);
        let wi = weekdays.iter().position(|w| &text[..3] == *w).unwrap();
        compare_parse(
            &format!("{}, 06-Nov-{year:02} 08:49:37 GMT", full_weekdays[wi]),
            counts,
        );
    }
    let quirk = "Sunday, 06-Nov-94x08:49:37 GMT";
    compare_parse(quirk, counts);
    assert!(verified::parse_http_date(quirk).is_ok());
    assert!(released::parse_http_date(quirk).is_ok());
    let mut state = SEED;
    for len in 0..=128 {
        for _ in 0..512 {
            let bytes: Vec<u8> = (0..len)
                .map(|_| {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    (state & 127) as u8
                })
                .collect();
            compare_parse(std::str::from_utf8(&bytes).unwrap(), counts);
        }
    }
}

fn error_and_panics(counts: &mut Counts) {
    let a = verified::parse_http_date("invalid").unwrap_err();
    let b = released::parse_http_date("invalid").unwrap_err();
    assert_eq!(a.description(), b.description());
    assert!(a.source().is_none() && b.source().is_none());
    assert!(a.cause().is_none() && b.cause().is_none());
    compare_formatting(&a, &b, counts);
    let ai = std::io::Error::from(a);
    let bi = std::io::Error::from(b);
    assert_eq!(ai.kind(), bi.kind());
    assert_eq!(ai.kind(), std::io::ErrorKind::Other);
    assert_eq!(ai.to_string(), bi.to_string());
    assert!(ai.get_ref().unwrap().is::<verified::Error>());
    assert!(bi.get_ref().unwrap().is::<released::Error>());
    assert!(ai
        .into_inner()
        .unwrap()
        .downcast::<verified::Error>()
        .is_ok());
    assert!(bi
        .into_inner()
        .unwrap()
        .downcast::<released::Error>()
        .is_ok());
    counts.error_observations += 1;
    for t in [
        UNIX_EPOCH - Duration::from_nanos(1),
        UNIX_EPOCH - Duration::from_secs(1),
        UNIX_EPOCH + Duration::from_secs(LIMIT),
        UNIX_EPOCH + Duration::new(LIMIT, 1),
    ] {
        assert!(catch_unwind(|| verified::HttpDate::from(t)).is_err());
        assert!(catch_unwind(|| released::HttpDate::from(t)).is_err());
        assert!(catch_unwind(|| verified::fmt_http_date(t)).is_err());
        assert!(catch_unwind(|| released::fmt_http_date(t)).is_err());
        counts.panic_observations += 2;
    }
}

fn main() {
    public_date_surface::<verified::HttpDate, verified::Error>();
    public_date_surface::<released::HttpDate, released::Error>();
    let mut counts = Counts::default();
    for day in 0..LIMIT / 86_400 {
        let s = day * 86_400 + 45_296;
        compare_instant(UNIX_EPOCH + Duration::from_secs(s));
        counts.civil_days += 1;
        if day % 997 == 0 {
            compare_traits(s, &mut counts);
        }
    }
    for s in [
        0,
        1,
        86_399,
        86_400,
        784_111_777,
        951_696_000,
        951_782_400,
        951_868_800,
        4_107_456_000,
        4_107_542_400,
        13_574_563_200,
        13_574_649_600,
        LIMIT - 86_400,
        LIMIT - 1,
    ] {
        for nanos in [0, 1, 999_999_999] {
            compare_instant(UNIX_EPOCH + Duration::new(s, nanos));
            counts.boundary_instants += 1;
        }
        compare_traits(s, &mut counts);
    }
    parser_corpus(&mut counts);
    // Silence only the deliberate caught panics. Any mismatch remains a failing process.
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|info| {
        let text = info
            .payload()
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| info.payload().downcast_ref::<String>().map(String::as_str));
        if !text.is_some_and(|t| {
            t == "controlled writer panic"
                || t == "date must be before year 9999"
                || t.starts_with("all times should be after the epoch")
        }) {
            eprintln!("{info}");
        }
    }));
    for s in [0, 784_111_777, 951_782_400, LIMIT - 1] {
        compare_formatting(
            &verified::HttpDate::from(UNIX_EPOCH + Duration::from_secs(s)),
            &released::HttpDate::from(UNIX_EPOCH + Duration::from_secs(s)),
            &mut counts,
        );
    }
    error_and_panics(&mut counts);
    std::panic::set_hook(previous_hook);
    assert_eq!(
        std::mem::size_of::<verified::HttpDate>(),
        std::mem::size_of::<released::HttpDate>()
    );
    assert_eq!(std::mem::size_of::<verified::HttpDate>(), 8);
    println!("{{\"status\":\"passed\",\"civil_days\":{},\"boundary_instants\":{},\"parser_inputs\":{},\"trait_pairs\":{},\"formatting_observations\":{},\"writer_observations\":{},\"panic_observations\":{},\"error_observations\":{},\"seed\":\"0x{:016x}\"}}",
        counts.civil_days, counts.boundary_instants, counts.parser_inputs, counts.trait_pairs,
        counts.formatting_observations, counts.writer_observations, counts.panic_observations,
        counts.error_observations, SEED);
}
