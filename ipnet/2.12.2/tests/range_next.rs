//! Finite boundary checks; universal returned-value/state coverage is in Lean.
use ipnet::Ipv4AddrRange;
use std::net::Ipv4Addr;

#[test]
fn next_matches_half_open_interval_and_remaining_state() {
    let max = u32::MAX;
    for (start, end) in [(0, 0), (max, max), (0, max), (1, 0), (max, 0),
                         (max - 2, max), (255, 257), (65535, 65537)] {
        let mut range = Ipv4AddrRange::new(Ipv4Addr::from(start), Ipv4Addr::from(end));
        let mut lower = u64::from(start);
        let upper = u64::from(end) + 1;
        for _ in 0..5 {
            let before = range;
            let expected = (lower < upper).then(|| Ipv4Addr::from(lower as u32));
            assert_eq!(range.next(), expected, "input {start}..={end}, lower {lower}");
            if expected.is_some() {
                lower += 1;
                let expected_state = if lower == upper {
                    Ipv4AddrRange::new(Ipv4Addr::from(1), Ipv4Addr::from(0))
                } else {
                    Ipv4AddrRange::new(Ipv4Addr::from(lower as u32), Ipv4Addr::from(end))
                };
                assert_eq!(range, expected_state);
            } else {
                assert_eq!(range, before);
            }
        }
    }
}
