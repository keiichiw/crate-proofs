//! Native boundary observations, separate from the universal Lean contracts.
use ipnet::Ipv6AddrRange;
use std::net::Ipv6Addr;

fn range(start: u128, end: u128) -> Ipv6AddrRange {
    Ipv6AddrRange::new(Ipv6Addr::from(start), Ipv6Addr::from(end))
}

#[test]
fn full_range_skip_and_hint_do_not_compute_overflowing_cardinality() {
    let mut front = range(0, u128::MAX);
    assert_eq!(front.size_hint(), (usize::MAX, None));
    assert_eq!(front.nth(usize::MAX), Some(Ipv6Addr::from(usize::MAX as u128)));
    assert_eq!(front.next(), Some(Ipv6Addr::from(usize::MAX as u128 + 1)));
    let mut back = range(0, u128::MAX);
    assert_eq!(back.nth_back(usize::MAX), Some(Ipv6Addr::from(u128::MAX - usize::MAX as u128)));
    assert_eq!(back.next_back(), Some(Ipv6Addr::from(u128::MAX - usize::MAX as u128 - 1)));
}

#[test]
fn exhaustion_remains_empty_across_front_and_back_operations() {
    for address in [0, 1, u128::MAX] {
        let mut r = range(address, address);
        assert_eq!(r.next_back(), Some(Ipv6Addr::from(address)));
        assert_eq!(r.next(), None);
        assert_eq!(r.nth(usize::MAX), None);
        assert_eq!(r.nth_back(usize::MAX), None);
        assert_eq!(r.next_back(), None);
        assert_eq!(r.size_hint(), (0, Some(0)));
    }
}

#[test]
#[cfg(debug_assertions)]
fn checked_count_distinguishes_usize_and_u128_overflow_boundaries() {
    assert_eq!(range(1, 0).count(), 0);
    assert_eq!(range(0, usize::MAX as u128 - 1).count(), usize::MAX);
    assert!(std::panic::catch_unwind(|| range(0, usize::MAX as u128).count()).is_err());
    assert!(std::panic::catch_unwind(|| range(0, u128::MAX).count()).is_err());
}

#[test]
fn standard_segment_constructor_preserves_network_byte_order() {
    for s in [
        [0; 8], [u16::MAX; 8],
        [0x0102, 0x0304, 0x0506, 0x0708, 0x090a, 0x0b0c, 0x0d0e, 0x0f10],
        [0xff00, 0x00ff, 0x8000, 0x0080, 0x7fff, 0xff7f, 1, 256],
    ] {
        let ip = Ipv6Addr::new(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]);
        let expected: Vec<u8> = s.iter().flat_map(|word| word.to_be_bytes()).collect();
        assert_eq!(ip.octets().as_slice(), expected.as_slice());
    }
}
