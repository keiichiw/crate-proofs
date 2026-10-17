//! Small native coverage witnesses; universal greedy partition claims require Lean.
use ipnet::{Ipv6Net, Ipv6Subnets};
use std::net::Ipv6Addr;

#[test]
fn whole_space_and_top_block_terminate_without_saturation_revival() {
    let mut all = Ipv6Subnets::new(Ipv6Addr::from(0), Ipv6Addr::from(u128::MAX), 0);
    assert_eq!(all.next(), Some(Ipv6Net::new(Ipv6Addr::from(0), 0).unwrap()));
    assert_eq!(all.next(), None);
    assert_eq!(all.next(), None);
    let top = u128::MAX - 15;
    let mut last = Ipv6Subnets::new(Ipv6Addr::from(top), Ipv6Addr::from(u128::MAX), 124);
    assert_eq!(last.next(), Some(Ipv6Net::new(Ipv6Addr::from(top), 124).unwrap()));
    assert_eq!(last.next(), None);
    assert_eq!(last.next(), None);
}

#[test]
fn small_unaligned_ranges_have_exact_canonical_greedy_cover() {
    for (start, end) in [(0, 0), (1, 17), (65529, 65550), (u128::MAX - 31, u128::MAX)] {
        for q in [0, 120, 124, 127, 128] {
            let blocks: Vec<_> = Ipv6Subnets::new(Ipv6Addr::from(start), Ipv6Addr::from(end), q).collect();
            let mut addresses = Vec::new();
            for block in blocks {
                let lo = u128::from(block.network());
                let hi = u128::from(block.broadcast());
                assert_eq!(block.addr(), block.network());
                assert!(block.prefix_len() >= q);
                assert!(start <= lo && hi <= end);
                if block.prefix_len() > q {
                    let parent = block.supernet().unwrap();
                    assert!(u128::from(parent.network()) != lo || u128::from(parent.broadcast()) > end);
                }
                addresses.extend(lo..=hi);
            }
            assert_eq!(addresses, (start..=end).collect::<Vec<_>>());
        }
    }
}
