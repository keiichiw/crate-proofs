//! Finite union checks independent of ipnet's endpoint/containment operations.
use ipnet::Ipv4Net;

fn interval(n: Ipv4Net) -> (u64, u64) {
    let width = 1u64 << (32 - n.prefix_len());
    let start = u64::from(u32::from(n.addr())) / width * width;
    (start, start + width)
}

fn check(input: Vec<Ipv4Net>) {
    let output = Ipv4Net::aggregate(&input);
    let before: Vec<_> = input.iter().copied().map(interval).collect();
    let after: Vec<_> = output.iter().copied().map(interval).collect();
    for (n, &(s, _)) in output.iter().zip(&after) {
        assert_eq!(u64::from(u32::from(n.addr())), s);
    }
    for pair in after.windows(2) {
        let ((s, e), (t, u)) = (pair[0], pair[1]);
        assert!(e <= t, "overlapping or unordered output");
        assert!(!(e == t && e - s == u - t && s % (2 * (e - s)) == 0),
            "mergeable siblings remain");
    }
    // Membership is constant between consecutive endpoints; testing each left
    // endpoint checks the complete union without enumerating 2^32 addresses.
    let mut endpoints = vec![0, 1u64 << 32];
    for &(s, e) in before.iter().chain(&after) {
        endpoints.extend([s, e]);
    }
    endpoints.sort_unstable();
    endpoints.dedup();
    for x in endpoints.into_iter().filter(|&x| x < 1u64 << 32) {
        assert_eq!(before.iter().any(|&(s, e)| s <= x && x < e),
            after.iter().any(|&(s, e)| s <= x && x < e));
    }
}

#[test]
fn aggregate_boundary_unions_and_noncanonical_inputs() {
    let addresses = [0, 1, 255, 256, 0x7fff_ffff, 0x8000_0000, u32::MAX - 1, u32::MAX];
    let mut candidates = Vec::new();
    for a in addresses {
        for p in 0..=32 {
            candidates.push(Ipv4Net::new(a.into(), p).unwrap());
        }
    }
    check(vec![]);
    for &a in &candidates {
        check(vec![a, a]);
        for &b in &candidates {
            check(vec![b, a, b]);
        }
    }
    // Every subset of one aligned eight-address block, at both address limits.
    for base in [0, u32::MAX - 7] {
        for bits in 0u16..256 {
            check((0..8).filter(|i| bits & (1 << i) != 0)
                .rev().map(|i| Ipv4Net::new((base + i).into(), 32).unwrap()).collect());
        }
    }
}
