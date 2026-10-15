use fork::AsciiSet as FSet;
use std::{borrow::Cow, fmt, fmt::Write as _};
use upstream::AsciiSet as USet;

const FC: &FSet = &FSet::EMPTY.add(b' ').add(b'+').add(b'%');
const UC: &USet = &USet::EMPTY.add(b' ').add(b'+').add(b'%');
const FU: &FSet = &FSet::EMPTY.add(b' ').union(FSet::EMPTY.add(b'+').add(b'%'));
const UU: &USet = &USet::EMPTY.add(b' ').union(USet::EMPTY.add(b'+').add(b'%'));
const FR: &FSet = &FSet::EMPTY.add(b' ').add(b'+').add(b'%').remove(b'+');
const UR: &USet = &USet::EMPTY.add(b' ').add(b'+').add(b'%').remove(b'+');
const FN: &FSet = &FSet::EMPTY.add(b'A').add(b'%').complement();
const UN: &USet = &USet::EMPTY.add(b'A').add(b'%').complement();

#[derive(Default)]
struct Counts {
    encode_cases: usize,
    encode_chunks: usize,
    encode_hints: usize,
    encode_clones: usize,
    decode_cases: usize,
    decode_bytes: usize,
    decode_hints: usize,
    decode_clones: usize,
    decode_cows: usize,
    utf8_results: usize,
    byte_checks: usize,
    set_ops: usize,
    high_panics: usize,
    utf8_wrapper_cases: usize,
    decode_str_wrapper_cases: usize,
    encode_eq_checks: usize,
    debug_format_checks: usize,
    single_escape_cow_checks: usize,
    invalid_owned_utf8_error_checks: usize,
    display_failure_cases: usize,
    display_write_events: usize,
    debug_sink_failure_cases: usize,
    debug_sink_write_events: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct DisplayTrace {
    writes: Vec<String>,
    failed: bool,
}

#[derive(Debug, PartialEq, Eq)]
struct DebugTrace {
    writes: Vec<String>,
    failed: bool,
}

struct RecordingWriter {
    writes: Vec<String>,
    fail_on: Option<usize>,
}

impl fmt::Write for RecordingWriter {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let index = self.writes.len();
        self.writes.push(value.to_owned());
        if self.fail_on == Some(index) {
            Err(fmt::Error)
        } else {
            Ok(())
        }
    }
}

fn display_trace(value: impl fmt::Display, fail_on: Option<usize>) -> DisplayTrace {
    let mut writer = RecordingWriter {
        writes: Vec::new(),
        fail_on,
    };
    let result = write!(&mut writer, "{value}");
    DisplayTrace {
        writes: writer.writes,
        failed: result.is_err(),
    }
}

fn debug_trace(value: &impl fmt::Debug, alternate: bool, fail_on: Option<usize>) -> DebugTrace {
    let mut writer = RecordingWriter {
        writes: Vec::new(),
        fail_on,
    };
    let result = if alternate {
        fmt::write(&mut writer, format_args!("{:#?}", value))
    } else {
        fmt::write(&mut writer, format_args!("{:?}", value))
    };
    DebugTrace {
        writes: writer.writes,
        failed: result.is_err(),
    }
}

fn compare_debug_sinks<A: fmt::Debug, B: fmt::Debug>(
    fork_value: &A,
    upstream_value: &B,
    counts: &mut Counts,
) {
    for alternate in [false, true] {
        let fork_success = debug_trace(fork_value, alternate, None);
        let upstream_success = debug_trace(upstream_value, alternate, None);
        assert_eq!(
            fork_success, upstream_success,
            "Debug sink trace alternate={alternate}"
        );
        assert!(!fork_success.failed);
        for fail_on in 0..fork_success.writes.len() {
            let fork_failure = debug_trace(fork_value, alternate, Some(fail_on));
            let upstream_failure = debug_trace(upstream_value, alternate, Some(fail_on));
            assert_eq!(
                fork_failure, upstream_failure,
                "failing Debug sink at {fail_on}, alternate={alternate}"
            );
            assert!(
                fork_failure.failed,
                "Debug should propagate sink error {fail_on}"
            );
            assert_eq!(fork_failure.writes.len(), fail_on + 1, "Debug write order");
            counts.debug_sink_failure_cases += 1;
            counts.debug_sink_write_events += fork_failure.writes.len();
        }
    }
}

fn compare_debug_sink_samples(counts: &mut Counts) {
    let bytes = b"A %Z";
    let fork_set = FC;
    let upstream_set = UC;
    compare_debug_sinks(fork_set, upstream_set, counts);

    let mut fork_encode = fork::percent_encode(bytes, fork_set);
    let mut upstream_encode = upstream::percent_encode(bytes, upstream_set);
    compare_debug_sinks(&fork_encode, &upstream_encode, counts);
    fork_encode.next();
    upstream_encode.next();
    compare_debug_sinks(&fork_encode, &upstream_encode, counts);

    let mut fork_decode = fork::percent_decode(b"a%20b%Q");
    let mut upstream_decode = upstream::percent_decode(b"a%20b%Q");
    compare_debug_sinks(&fork_decode, &upstream_decode, counts);
    fork_decode.next();
    upstream_decode.next();
    compare_debug_sinks(&fork_decode, &upstream_decode, counts);
}

fn compare_display_sinks(c: &mut Counts) {
    let input = b"ab c%+de";
    let fork_success = display_trace(fork::percent_encode(input, FC), None);
    let upstream_success = display_trace(upstream::percent_encode(input, UC), None);
    assert_eq!(fork_success, upstream_success, "recording Display sink");
    assert!(!fork_success.failed);
    for fail_on in 0..fork_success.writes.len() {
        let fork_trace = display_trace(fork::percent_encode(input, FC), Some(fail_on));
        let upstream_trace = display_trace(upstream::percent_encode(input, UC), Some(fail_on));
        assert_eq!(
            fork_trace, upstream_trace,
            "failing Display sink at {fail_on}"
        );
        assert!(
            fork_trace.failed,
            "Display should propagate sink error {fail_on}"
        );
        assert_eq!(fork_trace.writes.len(), fail_on + 1, "Display write order");
        c.display_failure_cases += 1;
        c.display_write_events += fork_trace.writes.len();
    }
}

fn single_escape_cow(c: &mut Counts) {
    for byte in [b' ', b'+', b'%'] {
        let input = [byte];
        let fork_cow: Cow<'_, str> = fork::percent_encode(&input, FC).into();
        let upstream_cow: Cow<'_, str> = upstream::percent_encode(&input, UC).into();
        assert_eq!(fork_cow, upstream_cow, "single escape Cow for {byte}");
        assert!(
            matches!(fork_cow, Cow::Borrowed(_)),
            "fork single escape borrows {byte}"
        );
        assert!(
            matches!(upstream_cow, Cow::Borrowed(_)),
            "upstream single escape borrows {byte}"
        );
        c.single_escape_cow_checks += 1;
    }
}

fn invalid_owned_utf8_errors(c: &mut Counts) {
    // Percent escapes force percent_decode's Cow<[u8]> result to be owned.
    for input in [
        b"%C3".as_slice(),
        b"%E2%82",
        b"%F0%90%80",
        b"A%C3%28",
        b"%ED%A0%80",
        b"%F4%90%80%80",
    ] {
        let fork_result = fork::percent_decode(input).decode_utf8();
        let upstream_result = upstream::percent_decode(input).decode_utf8();
        match (fork_result, upstream_result) {
            (Err(fork_error), Err(upstream_error)) => {
                assert_eq!(
                    fork_error.valid_up_to(),
                    upstream_error.valid_up_to(),
                    "owned valid_up_to {input:?}"
                );
                assert_eq!(
                    fork_error.error_len(),
                    upstream_error.error_len(),
                    "owned error_len {input:?}"
                );
            }
            (fork_result, upstream_result) => panic!(
                "owned invalid UTF-8 result differs {input:?}: {fork_result:?} {upstream_result:?}"
            ),
        }
        c.invalid_owned_utf8_error_checks += 1;
    }
}

fn encode(input: &[u8], fs: &'static FSet, us: &'static USet, c: &mut Counts) {
    let f_cow: Cow<'_, str> = fork::percent_encode(input, fs).into();
    let u_cow: Cow<'_, str> = upstream::percent_encode(input, us).into();
    assert_eq!(
        f_cow.as_ref(),
        u_cow.as_ref(),
        "encode Cow content {input:?}"
    );
    assert_eq!(
        matches!(f_cow, Cow::Borrowed(_)),
        matches!(u_cow, Cow::Borrowed(_)),
        "encode Cow borrow {input:?}"
    );
    let mut f = fork::percent_encode(input, fs);
    let mut u = upstream::percent_encode(input, us);
    assert_eq!(
        format!("{:?}", f),
        format!("{:?}", u),
        "encode Debug {input:?}"
    );
    assert_eq!(
        format!("{:#?}", f),
        format!("{:#?}", u),
        "alternate encode Debug {input:?}"
    );
    c.debug_format_checks += 2;
    let f_initial = f.clone();
    let u_initial = u.clone();
    assert_eq!(
        fork::percent_encode(input, fs).to_string(),
        upstream::percent_encode(input, us).to_string(),
        "encode Display {input:?}"
    );
    if let Ok(text) = std::str::from_utf8(input) {
        assert_eq!(
            fork::utf8_percent_encode(text, fs).to_string(),
            upstream::utf8_percent_encode(text, us).to_string(),
            "utf8_percent_encode wrapper {input:?}"
        );
        c.utf8_wrapper_cases += 1;
    }
    c.encode_cases += 1;
    loop {
        assert_eq!(f.size_hint(), u.size_hint(), "encode hint {input:?}");
        c.encode_hints += 1;
        match (f.next(), u.next()) {
            (Some(a), Some(b)) => {
                assert_eq!(a, b, "encode chunk {input:?}");
                c.encode_chunks += 1;
                let f_same = f.clone();
                let u_same = u.clone();
                assert_eq!(f == f_same, u == u_same, "encode clone equality {input:?}");
                assert_eq!(
                    f == f_initial,
                    u == u_initial,
                    "partially consumed encode equality {input:?}"
                );
                c.encode_eq_checks += 2;
                assert_eq!(
                    format!("{:?}", f),
                    format!("{:?}", u),
                    "partial encode Debug {input:?}"
                );
                assert_eq!(
                    format!("{:#?}", f),
                    format!("{:#?}", u),
                    "partial alternate encode Debug {input:?}"
                );
                c.debug_format_checks += 2;
                let mut fc = f.clone();
                let mut uc = u.clone();
                assert_eq!(
                    fc.by_ref().map(str::to_owned).collect::<Vec<_>>(),
                    uc.by_ref().map(str::to_owned).collect::<Vec<_>>(),
                    "encode clone {input:?}"
                );
                c.encode_clones += 1;
                let fcow: Cow<'_, str> = f.clone().into();
                let ucow: Cow<'_, str> = u.clone().into();
                assert_eq!(fcow.as_ref(), ucow.as_ref(), "encode suffix Cow {input:?}");
                assert_eq!(
                    matches!(fcow, Cow::Borrowed(_)),
                    matches!(ucow, Cow::Borrowed(_)),
                    "encode suffix Cow borrow {input:?}"
                );
            }
            (None, None) => break,
            (a, b) => panic!("encode termination {input:?}: {a:?} {b:?}"),
        }
    }
    assert_eq!(
        f.size_hint(),
        u.size_hint(),
        "terminal encode hint {input:?}"
    );
    c.encode_hints += 1;
}
fn decode(input: &[u8], c: &mut Counts) {
    let mut f = fork::percent_decode(input);
    let mut u = upstream::percent_decode(input);
    assert_eq!(
        format!("{:?}", f),
        format!("{:?}", u),
        "decode Debug {input:?}"
    );
    assert_eq!(
        format!("{:#?}", f),
        format!("{:#?}", u),
        "alternate decode Debug {input:?}"
    );
    c.debug_format_checks += 2;
    c.decode_cases += 1;
    loop {
        assert_eq!(f.size_hint(), u.size_hint(), "decode hint {input:?}");
        c.decode_hints += 1;
        match (f.next(), u.next()) {
            (Some(a), Some(b)) => {
                assert_eq!(a, b, "decode byte {input:?}");
                c.decode_bytes += 1;
                assert_eq!(
                    format!("{:?}", f),
                    format!("{:?}", u),
                    "partial decode Debug {input:?}"
                );
                assert_eq!(
                    format!("{:#?}", f),
                    format!("{:#?}", u),
                    "partial alternate decode Debug {input:?}"
                );
                c.debug_format_checks += 2;
                let mut fc = f.clone();
                let mut uc = u.clone();
                assert_eq!(
                    fc.by_ref().collect::<Vec<_>>(),
                    uc.by_ref().collect::<Vec<_>>(),
                    "decode clone {input:?}"
                );
                c.decode_clones += 1;
                let fcow: Cow<'_, [u8]> = f.clone().into();
                let ucow: Cow<'_, [u8]> = u.clone().into();
                assert_eq!(fcow.as_ref(), ucow.as_ref(), "decode suffix Cow {input:?}");
                assert_eq!(
                    matches!(fcow, Cow::Borrowed(_)),
                    matches!(ucow, Cow::Borrowed(_)),
                    "decode suffix Cow borrow {input:?}"
                );
                c.decode_cows += 1;
                match (f.clone().decode_utf8(), u.clone().decode_utf8()) {
                    (Ok(a), Ok(b)) => {
                        assert_eq!(a.as_ref(), b.as_ref(), "suffix strict UTF-8 {input:?}");
                        assert_eq!(
                            matches!(a, Cow::Borrowed(_)),
                            matches!(b, Cow::Borrowed(_)),
                            "suffix strict UTF-8 borrow {input:?}"
                        );
                    }
                    (Err(a), Err(b)) => {
                        assert_eq!(
                            a.valid_up_to(),
                            b.valid_up_to(),
                            "suffix valid_up_to {input:?}"
                        );
                        assert_eq!(a.error_len(), b.error_len(), "suffix error_len {input:?}");
                    }
                    (a, b) => panic!("suffix strict UTF-8 differs {input:?}: {a:?} {b:?}"),
                }
                c.utf8_results += 1;
                let fl = f.clone().decode_utf8_lossy();
                let ul = u.clone().decode_utf8_lossy();
                assert_eq!(fl.as_ref(), ul.as_ref(), "suffix lossy UTF-8 {input:?}");
                assert_eq!(
                    matches!(fl, Cow::Borrowed(_)),
                    matches!(ul, Cow::Borrowed(_)),
                    "suffix lossy UTF-8 borrow {input:?}"
                );
                c.utf8_results += 1;
            }
            (None, None) => break,
            (a, b) => panic!("decode termination {input:?}: {a:?} {b:?}"),
        }
    }
    assert_eq!(
        f.size_hint(),
        u.size_hint(),
        "terminal decode hint {input:?}"
    );
    c.decode_hints += 1;
    if let Ok(text) = std::str::from_utf8(input) {
        let f: Cow<'_, [u8]> = fork::percent_decode_str(text).into();
        let u: Cow<'_, [u8]> = upstream::percent_decode_str(text).into();
        assert_eq!(
            f.as_ref(),
            u.as_ref(),
            "percent_decode_str wrapper {input:?}"
        );
        assert_eq!(
            matches!(f, Cow::Borrowed(_)),
            matches!(u, Cow::Borrowed(_)),
            "percent_decode_str borrowing {input:?}"
        );
        c.decode_str_wrapper_cases += 1;
    }
    let fc: Cow<'_, [u8]> = fork::percent_decode(input).into();
    let uc: Cow<'_, [u8]> = upstream::percent_decode(input).into();
    assert_eq!(fc.as_ref(), uc.as_ref(), "decode Cow content {input:?}");
    assert_eq!(
        matches!(fc, Cow::Borrowed(_)),
        matches!(uc, Cow::Borrowed(_)),
        "decode Cow borrow {input:?}"
    );
    c.decode_cows += 1;
    match (
        fork::percent_decode(input).decode_utf8(),
        upstream::percent_decode(input).decode_utf8(),
    ) {
        (Ok(a), Ok(b)) => {
            assert_eq!(a.as_ref(), b.as_ref(), "strict UTF-8 content {input:?}");
            assert_eq!(
                matches!(a, Cow::Borrowed(_)),
                matches!(b, Cow::Borrowed(_)),
                "strict UTF-8 borrow {input:?}"
            );
        }
        (Err(a), Err(b)) => {
            assert_eq!(a.valid_up_to(), b.valid_up_to(), "valid_up_to {input:?}");
            assert_eq!(a.error_len(), b.error_len(), "error_len {input:?}");
        }
        (a, b) => panic!("strict UTF-8 result {input:?}: {a:?} {b:?}"),
    }
    c.utf8_results += 1;
    let f = fork::percent_decode(input).decode_utf8_lossy();
    let u = upstream::percent_decode(input).decode_utf8_lossy();
    assert_eq!(f.as_ref(), u.as_ref(), "lossy UTF-8 {input:?}");
    assert_eq!(
        matches!(f, Cow::Borrowed(_)),
        matches!(u, Cow::Borrowed(_)),
        "lossy UTF-8 borrow {input:?}"
    );
    c.utf8_results += 1;
}
fn check(input: &[u8], c: &mut Counts) {
    for (f, u) in [
        (&FSet::EMPTY, &USet::EMPTY),
        (fork::CONTROLS, upstream::CONTROLS),
        (fork::NON_ALPHANUMERIC, upstream::NON_ALPHANUMERIC),
        (FC, UC),
        (FU, UU),
        (FR, UR),
        (FN, UN),
    ] {
        encode(input, f, u, c);
    }
    decode(input, c);
}
fn set_ops(c: &mut Counts) {
    let pairs = [
        (
            FSet::EMPTY.add(b'A').add(b' ').add(b'%').add(b'Z'),
            USet::EMPTY.add(b'A').add(b' ').add(b'%').add(b'Z'),
        ),
        (
            FSet::EMPTY.add(b'A').add(b' ').add(b'%').remove(b'A'),
            USet::EMPTY.add(b'A').add(b' ').add(b'%').remove(b'A'),
        ),
        (
            FSet::EMPTY.add(b'A').add(b' ').add(b'%').union(FSet::EMPTY),
            USet::EMPTY.add(b'A').add(b' ').add(b'%').union(USet::EMPTY),
        ),
        (
            FSet::EMPTY.add(b'A') + FSet::EMPTY.add(b'B').add(b'+'),
            USet::EMPTY.add(b'A') + USet::EMPTY.add(b'B').add(b'+'),
        ),
        (
            FSet::EMPTY.add(b'A').add(b'%').complement(),
            USet::EMPTY.add(b'A').add(b'%').complement(),
        ),
        (
            !FSet::EMPTY.add(b'A').add(b'%'),
            !USet::EMPTY.add(b'A').add(b'%'),
        ),
        (FSet::EMPTY, USet::EMPTY),
    ];
    for (f, u) in pairs {
        assert_eq!(format!("{f:?}"), format!("{u:?}"), "AsciiSet Debug");
        assert_eq!(
            format!("{f:#?}"),
            format!("{u:#?}"),
            "AsciiSet alternate Debug"
        );
        c.debug_format_checks += 2;
        assert_eq!(
            f == FSet::EMPTY.add(b'A').add(b' ').add(b'%'),
            u == USet::EMPTY.add(b'A').add(b' ').add(b'%'),
            "AsciiSet equality"
        );
        let bytes: Vec<u8> = (0..=u8::MAX).collect();
        let fset: &'static FSet = Box::leak(Box::new(f));
        let uset: &'static USet = Box::leak(Box::new(u));
        assert_eq!(
            fork::percent_encode(&bytes, fset).collect::<String>(),
            upstream::percent_encode(&bytes, uset).collect::<String>(),
            "AsciiSet observable membership"
        );
        c.set_ops += 1;
    }
    // Normalize expected panic output and compare whether each high-byte operation panics.
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    for b in [128u8, 255] {
        let fa = std::panic::catch_unwind(|| {
            let _ = FSet::EMPTY.add(b);
        })
        .is_err();
        let ua = std::panic::catch_unwind(|| {
            let _ = USet::EMPTY.add(b);
        })
        .is_err();
        let fr = std::panic::catch_unwind(|| {
            let _ = FSet::EMPTY.remove(b);
        })
        .is_err();
        let ur = std::panic::catch_unwind(|| {
            let _ = USet::EMPTY.remove(b);
        })
        .is_err();
        assert_eq!(fa, ua, "add panic {b}");
        assert_eq!(fr, ur, "remove panic {b}");
        c.high_panics += 2;
    }
    std::panic::set_hook(hook);
}
fn main() {
    let mut c = Counts::default();
    compare_debug_sink_samples(&mut c);
    compare_display_sinks(&mut c);
    single_escape_cow(&mut c);
    invalid_owned_utf8_errors(&mut c);
    set_ops(&mut c);
    for b in 0..=u8::MAX {
        assert_eq!(
            fork::percent_encode_byte(b),
            upstream::percent_encode_byte(b),
            "percent_encode_byte {b}"
        );
        c.byte_checks += 1;
    }
    let targeted: Vec<Vec<u8>> = vec![
        b"%".to_vec(),
        b"%0".to_vec(),
        b"%GG".to_vec(),
        b"%0G".to_vec(),
        b"%%41".to_vec(),
        b"%25".to_vec(),
        b"%C3%A9".to_vec(),
        b"%E2%82%AC".to_vec(),
        b"%F0%9F%92%A9".to_vec(),
        b"%C3%28".to_vec(),
        b"%E2%28%A1".to_vec(),
        b"%F0%28%8C%BC".to_vec(),
        b"%E2%82".to_vec(),
        b"%F0%9F%92".to_vec(),
        b"%ED%A0%80".to_vec(),
        b"%F4%90%80%80".to_vec(),
        b"%80%BF".to_vec(),
        "plain UTF-8 💩".as_bytes().to_vec(),
        b"+%2B%20%2b".to_vec(),
        b"%00".to_vec(),
        b"%7F".to_vec(),
        b"%C0%AF".to_vec(),
        b"%E0%80%80".to_vec(),
        b"%F0%80%80%80".to_vec(),
    ];
    let mut targeted_count = 0;
    for s in &targeted {
        check(s, &mut c);
        targeted_count += 1;
    }
    let mut singleton = 0;
    for b in 0..=u8::MAX {
        check(&[b], &mut c);
        singleton += 1;
    }
    let mut pairs = 0;
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            check(&[a, b], &mut c);
            pairs += 1;
        }
    }
    let mut random = 0;
    let mut state = 0x9e37_79b9u32;
    for len in 0..=128 {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            v.push(state as u8);
        }
        check(&v, &mut c);
        random += 1;
    }
    let total = singleton + pairs + random + targeted_count;
    let run_id = std::env::var("PERCENT_ENCODING_RUN_ID")
        .expect("run differential through run-full-scope.sh to set PERCENT_ENCODING_RUN_ID");
    println!("{{\"run_id\":\"{run_id}\",\"status\":\"passed\",\"singleton_inputs\":{singleton},\"pair_inputs\":{pairs},\"random_inputs\":{random},\"targeted_malformed_valid_percent_utf8_inputs\":{targeted_count},\"byte_input_total\":{total},\"sets_per_input\":7,\"encode_cases\":{},\"encode_chunks\":{},\"encode_size_hint_observations\":{},\"encode_clone_checks\":{},\"encode_eq_checks\":{},\"decode_cases\":{},\"decode_bytes\":{},\"decode_size_hint_observations\":{},\"decode_clone_checks\":{},\"decode_cow_checks\":{},\"utf8_result_checks\":{},\"invalid_owned_utf8_error_checks\":{},\"percent_encode_byte_checks\":{},\"ascii_set_operation_checks\":{},\"high_byte_panic_checks\":{},\"utf8_wrapper_cases\":{},\"decode_str_wrapper_cases\":{},\"debug_format_checks\":{},\"single_escape_cow_checks\":{},\"display_failure_cases\":{},\"display_write_events\":{},\"debug_sink_failure_cases\":{},\"debug_sink_write_events\":{}}}",
        c.encode_cases,c.encode_chunks,c.encode_hints,c.encode_clones,c.encode_eq_checks,c.decode_cases,c.decode_bytes,c.decode_hints,c.decode_clones,c.decode_cows,c.utf8_results,c.invalid_owned_utf8_error_checks,c.byte_checks,c.set_ops,c.high_panics,c.utf8_wrapper_cases,c.decode_str_wrapper_cases,c.debug_format_checks,c.single_escape_cow_checks,c.display_failure_cases,c.display_write_events,c.debug_sink_failure_cases,c.debug_sink_write_events);
}
