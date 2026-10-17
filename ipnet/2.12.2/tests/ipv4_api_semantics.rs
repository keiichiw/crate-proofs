//! Finite independent numeric checks, separate from formal coverage.
use ipnet::{Ipv4AddrRange, Ipv4Net};
use std::net::Ipv4Addr;

fn range(s: u64, e: u64) -> Ipv4AddrRange {
    Ipv4AddrRange::new(Ipv4Addr::from(s as u32), Ipv4Addr::from(e as u32))
}
fn bounds(a: u32, p: u8) -> (u64, u64) {
    let size = 1u64 << (32 - p);
    let lo = u64::from(a) / size * size;
    (lo, lo + size - 1)
}

#[test]
#[cfg(target_pointer_width = "64")]
fn ipv4_range_observers_and_skips_match_numeric_intervals() {
    let values = [0, 1, 255, 256, 65535, 65536, u64::from(u32::MAX) - 1, u64::from(u32::MAX)];
    for s in values {
        for e in values {
            let r = range(s, e);
            let count = if s <= e { e - s + 1 } else { 0 };
            assert_eq!(r.count() as u64, count);
            assert_eq!(r.size_hint(), (count as usize, Some(count as usize)));
            let first = (s <= e).then(|| Ipv4Addr::from(s as u32));
            let last = (s <= e).then(|| Ipv4Addr::from(e as u32));
            assert_eq!(Iterator::min(r), first);
            assert_eq!(Iterator::max(r), last);
            assert_eq!(r.last(), last);
            let mut back = r;
            assert_eq!(back.next_back(), last);
            assert_eq!(back, if s > e { r } else if s == e { range(1, 0) } else { range(s, e - 1) });
            for n in [0, 1, count.saturating_sub(1), count, count + 1, u64::MAX] {
                let mut forward = r;
                let mut backward = r;
                let expected_f = (n < count).then(|| Ipv4Addr::from((s + n) as u32));
                let expected_b = (n < count).then(|| Ipv4Addr::from((e - n) as u32));
                assert_eq!(forward.nth(n as usize), expected_f);
                assert_eq!(backward.nth_back(n as usize), expected_b);
                let exhausted = n >= count.saturating_sub(1);
                assert_eq!(forward, if exhausted { range(1, 0) } else { range(s + n + 1, e) });
                assert_eq!(backward, if exhausted { range(1, 0) } else { range(s, e - n - 1) });
                if exhausted {
                    assert_eq!(forward.next_back(), None);
                    assert_eq!(backward.next(), None);
                }
            }
        }
    }
}

#[test]
fn ipv4_net_parent_hosts_and_subnet_initialization_all_prefixes() {
    let values = [0, 1, 255, 256, 0x7fff_ffff, 0x8000_0000, u32::MAX];
    for p in 0..=32 {
        for a in values {
            let net = Ipv4Net::new(Ipv4Addr::from(a), p).unwrap();
            let (lo, hi) = bounds(a, p);
            let (hs, he) = if p < 31 { (lo + 1, hi - 1) } else { (lo, hi) };
            assert_eq!(net.hosts(), range(hs, he));
            if p == 0 {
                assert_eq!(net.supernet(), None);
                assert!(!net.is_sibling(&net));
            } else {
                let parent_lo = bounds(a, p - 1).0;
                let parent = net.supernet().unwrap();
                assert_eq!(parent.prefix_len(), p - 1);
                assert_eq!(u64::from(u32::from(parent.addr())), parent_lo);
                assert!(net.is_sibling(&net));
                for b in values {
                    let other = Ipv4Net::new(Ipv4Addr::from(b), p).unwrap();
                    assert_eq!(net.is_sibling(&other), parent_lo == bounds(b, p - 1).0);
                }
            }
            for q in 0..=255 {
                let result = net.subnets(q);
                if q < p || q > 32 {
                    assert!(result.is_err());
                } else {
                    assert_eq!(result.unwrap(), ipnet::Ipv4Subnets::new(
                        Ipv4Addr::from(lo as u32), Ipv4Addr::from(hi as u32), q));
                }
            }
            let single = Ipv4Net::from(Ipv4Addr::from(a));
            assert_eq!((single.addr(), single.prefix_len()), (Ipv4Addr::from(a), 32));
        }
    }
    assert_eq!(Ipv4Net::default(), Ipv4Net::new(Ipv4Addr::UNSPECIFIED, 0).unwrap());
}

#[test]
fn ipv4_public_arithmetic_clamps_at_both_ends() {
    use ipnet::{IpAdd, IpSub};
    for a in [0, 1, 255, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
        for d in [0, 1, 256, 0x8000_0000, u32::MAX] {
            let addr = Ipv4Addr::from(a);
            let sum = (u64::from(a) + u64::from(d)).min(u64::from(u32::MAX));
            let difference = (i64::from(a) - i64::from(d)).max(0) as u32;
            assert_eq!(u32::from(addr.saturating_add(d)), sum as u32);
            assert_eq!(u32::from(addr.saturating_sub(d)), difference);
            let distance: u32 = addr.saturating_sub(Ipv4Addr::from(d));
            assert_eq!(distance, difference);
        }
    }
}

#[test]
fn ipv4_masks_preserve_address_and_reject_holes() {
    let masks: Vec<(u32, u8)> = (0..=32)
        .map(|p| (((1u64 << 32) - (1u64 << (32 - p))) as u32, p))
        .collect();
    for (mask, p) in &masks {
        assert_eq!(ipnet::ipv4_mask_to_prefix(Ipv4Addr::from(*mask)), Ok(*p));
        let a = Ipv4Addr::new(203, 0, 113, 199);
        let n = Ipv4Net::with_netmask(a, Ipv4Addr::from(*mask)).unwrap();
        assert_eq!((n.addr(), n.prefix_len()), (a, *p));
        for bit in 0..32 {
            let changed = mask ^ (1u32 << bit);
            let expected = masks.iter().find(|(m, _)| *m == changed).map(|(_, p)| *p);
            let parsed = ipnet::ipv4_mask_to_prefix(Ipv4Addr::from(changed));
            assert_eq!(parsed.ok(), expected);
            assert_eq!(Ipv4Net::with_netmask(a, Ipv4Addr::from(changed)).ok()
                .map(|n| (n.addr(), n.prefix_len())), expected.map(|p| (a, p)));
        }
    }
}

#[test]
fn ipv4_bitwise_overloads_preserve_network_byte_order() {
    use ipnet::{IpBitAnd, IpBitOr};
    let a = Ipv4Addr::from(0x1234_5678u32);
    let b = 0x00ff_00ffu32;
    assert_eq!(a.bitand(b), Ipv4Addr::new(0, 52, 0, 120));
    assert_eq!(a.bitand(Ipv4Addr::from(b)), Ipv4Addr::new(0, 52, 0, 120));
    assert_eq!(a.bitor(b), Ipv4Addr::new(18, 255, 86, 255));
    assert_eq!(a.bitor(Ipv4Addr::from(b)), Ipv4Addr::new(18, 255, 86, 255));
}
