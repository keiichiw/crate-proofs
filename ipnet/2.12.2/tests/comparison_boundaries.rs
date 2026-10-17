//! Finite checks of comparison/endian/public-dispatch boundaries, not proofs.
use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use std::cmp::Ordering;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

#[test]
fn address_order_uses_the_first_differing_high_digit() {
    let v4_hi = Ipv4Addr::new(1, 0, 0, 0);
    let v4_lo = Ipv4Addr::new(0, 255, 255, 255);
    assert_eq!(v4_hi.cmp(&v4_lo), Ordering::Greater);
    assert_eq!(v4_lo.partial_cmp(&v4_hi), Some(Ordering::Less));
    assert_eq!(v4_hi.cmp(&v4_hi), Ordering::Equal);

    let v6_lo = Ipv6Addr::new(
        0x00ff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    );
    let v6_hi = Ipv6Addr::new(0x0100, 0, 0, 0, 0, 0, 0, 0);
    assert_eq!(v6_lo.cmp(&v6_hi), Ordering::Less);
    assert_eq!(v6_hi.partial_cmp(&v6_lo), Some(Ordering::Greater));
    assert_eq!(v6_hi.cmp(&v6_hi), Ordering::Equal);
}

#[test]
fn asymmetric_bytes_form_big_endian_segments() {
    let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let addr = Ipv6Addr::from(bytes);
    assert_eq!(
        addr.segments(),
        [0x0102, 0x0304, 0x0506, 0x0708, 0x090a, 0x0b0c, 0x0d0e, 0x0f10]
    );
    assert_eq!(addr.octets(), bytes);
    let byte_value = bytes.iter().fold(0u128, |n, &b| n * 256 + u128::from(b));
    let segment_value = addr
        .segments()
        .iter()
        .fold(0u128, |n, &s| n * 65536 + u128::from(s));
    assert_eq!(byte_value, segment_value);
    assert_eq!(u128::from(addr), byte_value);
}

#[test]
fn public_contains_preserves_sets_and_family_for_noncanonical_inputs() {
    let n = Ipv4Net::new(Ipv4Addr::new(10, 0, 0, 1), 24).unwrap();
    let same_set = Ipv4Net::new(Ipv4Addr::new(10, 0, 0, 2), 24).unwrap();
    assert_ne!(n, same_set);
    assert!(n.contains(&same_set) && same_set.contains(&n));
    for (a, expected) in [
        (Ipv4Addr::new(10, 0, 0, 0), true),
        (Ipv4Addr::new(10, 0, 0, 255), true),
        (Ipv4Addr::new(9, 255, 255, 255), false),
        (Ipv4Addr::new(10, 0, 1, 0), false),
    ] {
        assert_eq!(n.contains(&a), expected);
        assert_eq!(IpNet::from(n).contains(&IpAddr::V4(a)), expected);
    }
    assert!(IpNet::from(n).contains(&IpNet::from(same_set)));
    let all4 = IpNet::from(Ipv4Net::new(Ipv4Addr::UNSPECIFIED, 0).unwrap());
    let all6 = IpNet::from(Ipv6Net::new(Ipv6Addr::UNSPECIFIED, 0).unwrap());
    let mapped = Ipv4Addr::new(10, 0, 0, 1).to_ipv6_mapped();
    assert!(!all4.contains(&IpAddr::V6(mapped)));
    assert!(!all6.contains(&IpAddr::V4(n.addr())));
    assert!(!all4.contains(&all6));
    assert!(!all6.contains(&all4));
    assert!(all6.contains(&IpAddr::V6(mapped)));
}
