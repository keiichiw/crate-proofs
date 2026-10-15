//! Exact typed hash recipe and equality compatibility of the public date.
use super::HttpDate;
#[cfg(creusot)]
use super::{valid_datetime_injective, RawDate};
#[cfg(creusot)]
use crate::stdlib_specs::{hash_state, hash_step_u16, hash_step_u8, supported_hasher};
#[cfg(creusot)]
use creusot_std::prelude::{ensures, logic, requires, DeepModel, Int};
use std::hash::{Hash, Hasher};

#[cfg(creusot)]
#[logic(open(self), inline)]
fn date_hash_effect<H: Hasher>(s: Int, d: RawDate) -> Int {
    let s = hash_step_u8::<H>(s, d.sec);
    let s = hash_step_u8::<H>(s, d.min);
    let s = hash_step_u8::<H>(s, d.hour);
    let s = hash_step_u8::<H>(s, d.day);
    let s = hash_step_u8::<H>(s, d.mon);
    let s = hash_step_u16::<H>(s, d.year);
    hash_step_u8::<H>(s, d.wday)
}

impl Hash for HttpDate {
    #[cfg_attr(creusot, requires(supported_hasher::<H>()))]
    #[cfg_attr(creusot, ensures(hash_state(&^state) == date_hash_effect::<H>(hash_state(&*state), self.raw_model())))]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Preserve derive's field order and primitive typed Hash dispatch.
        self.sec.hash(state);
        self.min.hash(state);
        self.hour.hash(state);
        self.day.hash(state);
        self.mon.hash(state);
        self.year.hash(state);
        self.wday.hash(state);
    }
}

#[cfg(creusot)]
#[requires(supported_hasher::<H>())]
#[requires(a.deep_model() == b.deep_model())]
#[requires(hash_state(&*left) == hash_state(&*right))]
#[ensures(result.0 == result.1)]
fn equal_dates_hash_equally<H: Hasher>(
    a: HttpDate,
    b: HttpDate,
    left: &mut H,
    right: &mut H,
) -> (u64, u64) {
    valid_datetime_injective(a.as_raw(), b.as_raw());
    a.hash(left);
    b.hash(right);
    (H::finish(&*left), H::finish(&*right))
}

#[cfg(creusot)]
#[requires(a.deep_model() == b.deep_model())]
#[ensures(result.0 == result.1)]
fn default_hasher_equality(a: HttpDate, b: HttpDate) -> (u64, u64) {
    let mut left = std::hash::DefaultHasher::new();
    let mut right = std::hash::DefaultHasher::new();
    equal_dates_hash_equally(a, b, &mut left, &mut right)
}
