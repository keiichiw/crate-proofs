use super::HttpDate;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::time::{Duration, UNIX_EPOCH};

#[path = "../../../verification/trial/reference/date.rs"]
mod upstream;

#[derive(Debug, PartialEq, Eq)]
enum WriteEvent {
    U8(u8),
    U16(u16),
}

#[derive(Default)]
struct TypedCallRecorder {
    events: Vec<WriteEvent>,
}

impl Hasher for TypedCallRecorder {
    fn finish(&self) -> u64 {
        0
    }

    fn write(&mut self, _bytes: &[u8]) {
        panic!("unexpected Hasher::write call")
    }

    fn write_u8(&mut self, value: u8) {
        self.events.push(WriteEvent::U8(value));
    }

    fn write_u16(&mut self, value: u16) {
        self.events.push(WriteEvent::U16(value));
    }

    fn write_u32(&mut self, _value: u32) {
        panic!("unexpected Hasher::write_u32 call")
    }

    fn write_u64(&mut self, _value: u64) {
        panic!("unexpected Hasher::write_u64 call")
    }

    fn write_u128(&mut self, _value: u128) {
        panic!("unexpected Hasher::write_u128 call")
    }

    fn write_usize(&mut self, _value: usize) {
        panic!("unexpected Hasher::write_usize call")
    }

    fn write_i8(&mut self, _value: i8) {
        panic!("unexpected Hasher::write_i8 call")
    }

    fn write_i16(&mut self, _value: i16) {
        panic!("unexpected Hasher::write_i16 call")
    }

    fn write_i32(&mut self, _value: i32) {
        panic!("unexpected Hasher::write_i32 call")
    }

    fn write_i64(&mut self, _value: i64) {
        panic!("unexpected Hasher::write_i64 call")
    }

    fn write_i128(&mut self, _value: i128) {
        panic!("unexpected Hasher::write_i128 call")
    }

    fn write_isize(&mut self, _value: isize) {
        panic!("unexpected Hasher::write_isize call")
    }
}

#[derive(Clone, Copy)]
struct CalendarFields {
    sec: u8,
    min: u8,
    hour: u8,
    day: u8,
    month: u8,
    year: u16,
    weekday: u8,
}

fn expected_field_events(fields: CalendarFields) -> Vec<WriteEvent> {
    vec![
        WriteEvent::U8(fields.sec),
        WriteEvent::U8(fields.min),
        WriteEvent::U8(fields.hour),
        WriteEvent::U8(fields.day),
        WriteEvent::U8(fields.month),
        WriteEvent::U16(fields.year),
        WriteEvent::U8(fields.weekday),
    ]
}

fn record_hash<T: Hash>(value: &T) -> TypedCallRecorder {
    let mut recorder = TypedCallRecorder::default();
    value.hash(&mut recorder);
    recorder
}

fn default_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[test]
fn public_hash_writes_seven_typed_fields_in_upstream_order() {
    // Field values come from the calendar fixtures; the expected event helper
    // states the typed widths and field order independently of Hash::hash.
    let fixtures = [
        (
            0,
            CalendarFields {
                sec: 0,
                min: 0,
                hour: 0,
                day: 1,
                month: 1,
                year: 1970,
                weekday: 4,
            },
        ),
        (
            784_111_777,
            CalendarFields {
                sec: 37,
                min: 49,
                hour: 8,
                day: 6,
                month: 11,
                year: 1994,
                weekday: 7,
            },
        ),
        (
            951_782_400,
            CalendarFields {
                sec: 0,
                min: 0,
                hour: 0,
                day: 29,
                month: 2,
                year: 2000,
                weekday: 2,
            },
        ),
        (
            1_475_419_451,
            CalendarFields {
                sec: 11,
                min: 44,
                hour: 14,
                day: 2,
                month: 10,
                year: 2016,
                weekday: 7,
            },
        ),
    ];

    for (seconds, fields) in fixtures {
        let instant = UNIX_EPOCH + Duration::from_secs(seconds);
        let public = HttpDate::from(instant);
        let reference = upstream::HttpDate::from(instant);
        let expected = expected_field_events(fields);

        assert_eq!(record_hash(&public).events, expected);
        assert_eq!(record_hash(&reference).events, expected);
    }
}

#[test]
fn hash_slice_uses_the_default_per_item_stream_for_public_dates() {
    let seconds = [0, 784_111_777];
    let public = seconds.map(|value| HttpDate::from(UNIX_EPOCH + Duration::from_secs(value)));
    let reference =
        seconds.map(|value| upstream::HttpDate::from(UNIX_EPOCH + Duration::from_secs(value)));

    let mut public_combined = TypedCallRecorder::default();
    <HttpDate as Hash>::hash_slice(&public, &mut public_combined);
    let mut expected_public = record_hash(&public[0]).events;
    expected_public.extend(record_hash(&public[1]).events);
    assert_eq!(public_combined.events, expected_public);

    let mut reference_combined = TypedCallRecorder::default();
    <upstream::HttpDate as Hash>::hash_slice(&reference, &mut reference_combined);
    let mut expected_reference = record_hash(&reference[0]).events;
    expected_reference.extend(record_hash(&reference[1]).events);
    assert_eq!(reference_combined.events, expected_reference);
    assert_eq!(public_combined.events, reference_combined.events);
}

#[test]
fn equal_public_dates_have_equal_hash_streams_without_assuming_injective_hashing() {
    let whole_second = UNIX_EPOCH + Duration::from_secs(784_111_777);
    let a = HttpDate::from(whole_second);
    let b = HttpDate::from(whole_second + Duration::from_nanos(999_999_999));
    assert_eq!(a, b);
    assert_eq!(record_hash(&a).events, record_hash(&b).events);
    assert_eq!(default_hash(&a), default_hash(&b));

    struct NoopHasher;

    impl Hasher for NoopHasher {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _bytes: &[u8]) {}
    }

    let distinct = HttpDate::from(UNIX_EPOCH + Duration::from_secs(0));
    assert_ne!(a, distinct);
    let mut first = NoopHasher;
    let mut second = NoopHasher;
    a.hash(&mut first);
    distinct.hash(&mut second);
    assert_eq!(first.finish(), second.finish());
}
