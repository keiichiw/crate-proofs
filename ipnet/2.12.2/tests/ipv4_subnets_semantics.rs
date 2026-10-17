//! Finite greedy-CIDR checks against a direct mathematical candidate search.
use ipnet::Ipv4Subnets;
use std::net::Ipv4Addr;

fn check_trace(start: u32, end: u32, q: u8, max_steps: usize) {
    let mut actual = Ipv4Subnets::new(start.into(), end.into(), q);
    let mut s = u64::from(start);
    let stop = u64::from(end) + 1;
    for _ in 0..max_steps {
        if s >= stop {
            assert_eq!(actual.next(), None);
            assert_eq!(actual.next(), None);
            return;
        }
        let (prefix, width) = (q..=32).map(|p| (p, 1u64 << (32 - p)))
            .find(|(_, width)| s % width == 0 && s + width <= stop).unwrap();
        let net = actual.next().expect("nonempty valid interval");
        assert_eq!(net.prefix_len(), prefix, "s={s}, stop={stop}, q={q}");
        assert_eq!(net.addr(), Ipv4Addr::from(s as u32));
        assert_eq!(net.network(), net.addr());
        assert_eq!(u64::from(u32::from(net.broadcast())) + 1, s + width);
        s += width;
        if s < stop {
            assert_eq!(actual, Ipv4Subnets::new((s as u32).into(), end.into(), q));
        }
    }
}

#[test]
fn greedy_subnets_boundaries_and_short_intervals() {
    let max = u32::MAX;
    let endpoints = [0, 1, 2, 255, 256, 0x7fff_ffff, 0x8000_0000, max - 1, max];
    for s in endpoints {
        for e in endpoints {
            for q in 0..=32 {
                check_trace(s, e, q, 65);
            }
        }
    }
    for s in [0, 1, 127, 255, 65535, max - 255] {
        for length in [1, 2, 3, 7, 31, 129, 256] {
            let e = u64::from(s) + length - 1;
            if e <= u64::from(max) {
                for q in 0..=32 {
                    check_trace(s, e as u32, q, 257);
                }
            }
        }
    }
}
