use core::ops::{Bound, RangeBounds};
pub fn bound_value(b: Bound<&usize>, len: usize) -> (usize, usize) {
    let begin = match b {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n.checked_add(1).expect("out of range"),
        Bound::Unbounded => 0,
    };
    (begin, len)
}
pub fn trait_bound(range: impl RangeBounds<usize>, len: usize) -> (usize, usize) {
    let begin = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n.checked_add(1).expect("out of range"),
        Bound::Unbounded => 0,
    };
    (begin, len)
}
pub fn trait_bound_simple(range: impl RangeBounds<usize>, len: usize) -> (usize, usize) {
    let begin = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => 0,
    };
    (begin, len)
}
pub fn trait_bound_twice(range: impl RangeBounds<usize>, len: usize) -> (usize, usize) {
    let begin = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => len,
    };
    (begin, end)
}
pub fn two_callback_paths(range: impl RangeBounds<usize>, take_first: bool) -> usize {
    let first = if take_first {
        match range.start_bound() { Bound::Included(&n) | Bound::Excluded(&n) => n, Bound::Unbounded => 0 }
    } else {
        match range.end_bound() { Bound::Included(&n) | Bound::Excluded(&n) => n, Bound::Unbounded => 0 }
    };
    let second_bound = if take_first { range.end_bound() } else { range.start_bound() };
    let second = match second_bound { Bound::Included(&n) | Bound::Excluded(&n) => n, Bound::Unbounded => 0 };
    first.wrapping_add(second)
}
pub fn checked_path(flag: bool) -> usize {
    let n = if flag { usize::MAX } else { 0 };
    n + 1
}
pub fn mutable_path(x: &mut usize, flag: bool) -> usize {
    if flag { *x = 10; } else { *x = 20; }
    *x += 1;
    *x
}
pub fn early_return(flag: bool) -> usize {
    if flag { return 7; }
    9
}
pub fn break_path(flag: bool) -> usize {
    loop {
        if flag { break 3; }
        break 4;
    }
}
