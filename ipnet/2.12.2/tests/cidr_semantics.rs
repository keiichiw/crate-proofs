//! Independent arithmetic/interval regression checks, not universal proofs.
use ipnet::{IpNet, Ipv4AddrRange, Ipv4Net, Ipv4Subnets, Ipv6AddrRange, Ipv6Net, Ipv6Subnets};
use std::net::{Ipv4Addr, Ipv6Addr};

fn bounds(a: u128, p: u8, width: u8) -> (u128, u128) {
    assert!(p <= width);
    if p == 0 {
        return (
            0,
            if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            },
        );
    }
    let size = 1u128 << (width - p);
    let lo = a / size * size;
    (lo, lo + (size - 1))
}
fn v4(n: Ipv4Net) -> (u128, u128) {
    bounds(u32::from(n.addr()) as u128, n.prefix_len(), 32)
}
fn v6(n: Ipv6Net) -> (u128, u128) {
    bounds(u128::from(n.addr()), n.prefix_len(), 128)
}
fn union(mut xs: Vec<(u128, u128)>) -> Vec<(u128, u128)> {
    xs.sort_unstable();
    let mut out: Vec<(u128, u128)> = vec![];
    for (lo, hi) in xs {
        if let Some(last) = out.last_mut() {
            if lo <= last.1 || last.1.checked_add(1) == Some(lo) {
                last.1 = last.1.max(hi);
                continue;
            }
        }
        out.push((lo, hi));
    }
    out
}
fn step(seed: &mut u128) -> u128 {
    *seed = seed
        .wrapping_mul(0x2360ed051fc65da44385df649fccf645)
        .wrapping_add(1);
    *seed
}

#[test]
fn contains_all_prefixes_and_host_bits_against_intervals() {
    let mut seed = 0x123456789abcdefu128;
    for p in 0..=128u8 {
        let a = step(&mut seed);
        let n = Ipv6Net::new(Ipv6Addr::from(a), p).unwrap();
        let (lo, hi) = bounds(a, p, 128);
        for x in [
            0,
            u128::MAX,
            a,
            lo,
            hi,
            lo.saturating_sub(1),
            hi.saturating_add(1),
            step(&mut seed),
        ] {
            assert_eq!(n.contains(&Ipv6Addr::from(x)), lo <= x && x <= hi);
        }
        for q in [0, p, 128] {
            let m = Ipv6Net::new(Ipv6Addr::from(a), q).unwrap();
            let (ml, mh) = v6(m);
            assert_eq!(n.contains(&m), lo <= ml && mh <= hi);
        }
        assert!(!IpNet::from(n).contains(&IpNet::from(Ipv4Net::default())));
    }
    for p in 0..=32u8 {
        let a = step(&mut seed) as u32;
        let n = Ipv4Net::new(Ipv4Addr::from(a), p).unwrap();
        let (lo, hi) = bounds(a as u128, p, 32);
        for x in [
            0,
            u32::MAX,
            a,
            lo as u32,
            hi as u32,
            (lo as u32).saturating_sub(1),
            (hi as u32).saturating_add(1),
        ] {
            assert_eq!(
                n.contains(&Ipv4Addr::from(x)),
                lo <= x as u128 && x as u128 <= hi
            );
        }
        for q in [0, p, 32] {
            let m = Ipv4Net::new(Ipv4Addr::from(a), q).unwrap();
            let (ml, mh) = v4(m);
            assert_eq!(n.contains(&m), lo <= ml && mh <= hi);
        }
        assert!(!IpNet::from(n).contains(&IpNet::from(Ipv6Net::default())));
    }
}

#[test]
fn aggregation_preserves_exact_union_and_canonical_disjoint_output() {
    let mut seed = 42;
    for round in 0..160 {
        let count = round % 17;
        let mut a = vec![];
        let mut b = vec![];
        for _ in 0..count {
            let x = step(&mut seed);
            a.push(Ipv4Net::new(Ipv4Addr::from(x as u32), (x % 33) as u8).unwrap());
            b.push(Ipv6Net::new(Ipv6Addr::from(x), (x % 129) as u8).unwrap());
        }
        if round % 2 == 0 {
            a.push(Ipv4Net::new(Ipv4Addr::from(u32::MAX - 1), 32).unwrap());
            b.push(Ipv6Net::new(Ipv6Addr::from(u128::MAX - 1), 128).unwrap());
        }
        let aa = Ipv4Net::aggregate(&a);
        let bb = Ipv6Net::aggregate(&b);
        assert_eq!(
            union(a.iter().copied().map(v4).collect()),
            union(aa.iter().copied().map(v4).collect())
        );
        assert_eq!(
            union(b.iter().copied().map(v6).collect()),
            union(bb.iter().copied().map(v6).collect())
        );
        for n in &aa {
            assert_eq!(u32::from(n.addr()) as u128, v4(*n).0);
        }
        for n in &bb {
            assert_eq!(u128::from(n.addr()), v6(*n).0);
        }
        for xs in [
            aa.iter().copied().map(v4).collect::<Vec<_>>(),
            bb.iter().copied().map(v6).collect(),
        ] {
            for (i, x) in xs.iter().enumerate() {
                for y in &xs[i + 1..] {
                    assert!(x.1 < y.0 || y.1 < x.0);
                }
            }
        }
        let mixed: Vec<_> = a
            .into_iter()
            .map(IpNet::from)
            .chain(b.into_iter().map(IpNet::from))
            .collect();
        let agg = IpNet::aggregate(&mixed);
        assert_eq!(
            agg,
            aa.into_iter()
                .map(IpNet::from)
                .chain(bb.into_iter().map(IpNet::from))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn subnet_partitions_include_maximum_boundary_and_reversed_empty_ranges() {
    for end in [0u32, 1, 254, 255, u32::MAX - 1, u32::MAX] {
        let start = end.saturating_sub(17);
        for q in [0, 24, 31, 32] {
            let out: Vec<_> = Ipv4Subnets::new(start.into(), end.into(), q).collect();
            assert_eq!(
                union(out.iter().copied().map(v4).collect()),
                vec![(start as u128, end as u128)]
            );
            for n in out {
                assert!(n.prefix_len() >= q);
                assert_eq!(u32::from(n.addr()) as u128, v4(n).0);
            }
        }
    }
    for end in [0u128, 1, 254, 255, u128::MAX - 1, u128::MAX] {
        let start = end.saturating_sub(17);
        for q in [0, 64, 127, 128] {
            let out: Vec<_> = Ipv6Subnets::new(start.into(), end.into(), q).collect();
            assert_eq!(
                union(out.iter().copied().map(v6).collect()),
                vec![(start, end)]
            );
            for n in out {
                assert!(n.prefix_len() >= q);
                assert_eq!(u128::from(n.addr()), v6(n).0);
            }
        }
    }
    assert_eq!(Ipv4Subnets::new(2u32.into(), 1u32.into(), 255).next(), None);
    assert_eq!(
        Ipv6Subnets::new(2u128.into(), 1u128.into(), 255).next(),
        None
    );
}

#[test]
fn range_mixed_direction_and_skip_preserves_remaining_sequence() {
    for start in [0u128, 1, 255, u128::MAX - 20] {
        let mut r = Ipv6AddrRange::new(start.into(), (start + 20).into());
        let mut expected: std::collections::VecDeque<_> = (start..=start + 20).collect();
        assert_eq!(r.next().map(u128::from), expected.pop_front());
        assert_eq!(r.next_back().map(u128::from), expected.pop_back());
        for _ in 0..3 {
            expected.pop_front();
        }
        assert_eq!(r.nth(3).map(u128::from), expected.pop_front());
        for _ in 0..2 {
            expected.pop_back();
        }
        assert_eq!(r.nth_back(2).map(u128::from), expected.pop_back());
        assert_eq!(r.size_hint(), (expected.len(), Some(expected.len())));
        assert_eq!(
            r.collect::<Vec<_>>(),
            expected.into_iter().map(Ipv6Addr::from).collect::<Vec<_>>()
        );
    }
    let mut full = Ipv6AddrRange::new(0u128.into(), u128::MAX.into());
    assert_eq!(full.size_hint(), (usize::MAX, None));
    assert_eq!(
        full.nth(usize::MAX),
        Some(Ipv6Addr::from(usize::MAX as u128))
    );
    assert_eq!(full.next_back(), Some(Ipv6Addr::from(u128::MAX)));
    let mut r = Ipv4AddrRange::new((u32::MAX - 2).into(), u32::MAX.into());
    assert_eq!(r.nth_back(2), Some(Ipv4Addr::from(u32::MAX - 2)));
    assert_eq!(r.next(), None);
    assert_eq!(r.next_back(), None);
    assert_eq!(r.nth(usize::MAX), None);
}

#[test]
fn net_subnets_partition_noncanonical_networks_at_every_prefix() {
    for p in 0..=32u8 {
        let q = (p + 3).min(32);
        let n = Ipv4Net::new(Ipv4Addr::from(u32::MAX - 101), p).unwrap();
        let out: Vec<_> = n.subnets(q).unwrap().collect();
        assert_eq!(out.len(), 1usize << (q - p));
        assert_eq!(union(out.iter().copied().map(v4).collect()), vec![v4(n)]);
        for x in &out {
            assert_eq!(x.prefix_len(), q);
            assert_eq!(u32::from(x.addr()) as u128, v4(*x).0);
        }
        for pair in out.windows(2) {
            assert_eq!(v4(pair[0]).1 + 1, v4(pair[1]).0);
        }
        assert!(n.subnets(33).is_err());
        if p > 0 {
            assert!(n.subnets(p - 1).is_err());
        }
    }
    for p in 0..=128u8 {
        let q = (p + 3).min(128);
        let n = Ipv6Net::new(Ipv6Addr::from(u128::MAX - 101), p).unwrap();
        let out: Vec<_> = n.subnets(q).unwrap().collect();
        assert_eq!(out.len(), 1usize << (q - p));
        assert_eq!(union(out.iter().copied().map(v6).collect()), vec![v6(n)]);
        for x in &out {
            assert_eq!(x.prefix_len(), q);
            assert_eq!(u128::from(x.addr()), v6(*x).0);
        }
        for pair in out.windows(2) {
            assert_eq!(v6(pair[0]).1 + 1, v6(pair[1]).0);
        }
        assert!(n.subnets(129).is_err());
        if p > 0 {
            assert!(n.subnets(p - 1).is_err());
        }
    }
}

#[test]
fn hosts_endpoints_and_size_hint_use_full_mathematical_ranges() {
    for p in 0..=32u8 {
        let n = Ipv4Net::new(Ipv4Addr::from(u32::MAX - 101), p).unwrap();
        let (mut lo, mut hi) = v4(n);
        if p < 31 {
            lo += 1;
            hi -= 1;
        }
        assert_eq!(n.hosts().next().map(u32::from), Some(lo as u32));
        assert_eq!(n.hosts().next_back().map(u32::from), Some(hi as u32));
        let length = hi - lo + 1;
        let hint = if length <= usize::MAX as u128 {
            (length as usize, Some(length as usize))
        } else {
            (usize::MAX, None)
        };
        assert_eq!(n.hosts().size_hint(), hint);
    }
    for p in 0..=128u8 {
        let n = Ipv6Net::new(Ipv6Addr::from(u128::MAX - 101), p).unwrap();
        let (lo, hi) = v6(n);
        assert_eq!(n.hosts().next().map(u128::from), Some(lo));
        assert_eq!(n.hosts().next_back().map(u128::from), Some(hi));
        let length = (hi - lo).checked_add(1);
        let hint = match length {
            Some(x) if x <= usize::MAX as u128 => (x as usize, Some(x as usize)),
            _ => (usize::MAX, None),
        };
        assert_eq!(n.hosts().size_hint(), hint);
    }
}
