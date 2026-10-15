#![forbid(unsafe_code)]
#[cfg(all(creusot, any(feature = "probe-hash", feature = "probe-error")))]
use creusot_std::prelude::*;
#[cfg(feature = "probe-eq")]
mod eq_probe {
    #[cfg(creusot)]
    use creusot_std::prelude::{DeepModel, ensures};

    #[derive(Clone, Copy, DeepModel, PartialEq)]
    pub struct Date { pub year: u16, pub month: u8, pub day: u8 }

    #[cfg_attr(creusot, ensures(result == (a.deep_model() == b.deep_model())))]
    pub fn structural_eq(a: Date, b: Date) -> bool { a == b }
}

#[cfg(feature = "probe-ord")]
mod ord_probe {
    #[cfg(creusot)]
    use creusot_std::prelude::{ensures, logic, pearlite};
    use creusot_std::logic::ord::{partial_ord_laws_impl, OrdLogic, PartialOrdLogic};
    use creusot_std::model::DeepModel;
    use std::cmp::Ordering;

    #[derive(Clone, Copy)]
    pub struct Date { pub year: u16, pub month: u8, pub day: u8 }

    #[derive(Clone, Copy)]
    pub struct DateModel { pub year: u16, pub month: u8, pub day: u8 }

    impl DeepModel for Date {
        type DeepModelTy = DateModel;
        #[logic(open)]
        fn deep_model(self) -> DateModel {
            DateModel { year: self.year, month: self.month, day: self.day }
        }
    }

    impl PartialOrdLogic for DateModel {
        #[logic(open)]
        fn lt_log(self, other: Self) -> bool {
            pearlite! { self.year@ < other.year@ ||
                (self.year@ == other.year@ && (self.month@ < other.month@ ||
                    (self.month@ == other.month@ && self.day@ < other.day@))) }
        }
        partial_ord_laws_impl! {}
    }
    impl OrdLogic for DateModel {
        #[logic(law)]
        #[ensures(self < other || self == other || other < self)]
        fn lt_log_total(self, other: Self) {}
    }

    impl PartialEq for Date {
        fn eq(&self, other: &Self) -> bool { (self.year, self.month, self.day) == (other.year, other.month, other.day) }
    }
    impl Eq for Date {}
    impl PartialOrd for Date {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
    }
    impl Ord for Date {
        fn cmp(&self, other: &Self) -> Ordering {
            match self.year.cmp(&other.year) {
                Ordering::Equal => match self.month.cmp(&other.month) {
                    Ordering::Equal => self.day.cmp(&other.day),
                    ordering => ordering,
                },
                ordering => ordering,
            }
        }
    }

    #[cfg_attr(creusot, ensures(result == a.deep_model().cmp_log(b.deep_model())))]
    pub fn chronological_cmp(a: Date, b: Date) -> Ordering { a.cmp(&b) }
}

#[cfg(feature = "probe-hash")]
mod hash_probe {
    use std::hash::{DefaultHasher, Hash, Hasher};

    pub fn hash_via_default_hasher<T: Hash>(value: &T) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }
}

#[cfg(feature = "probe-error")]
mod error_probe {
    use std::{fmt, io};

    #[derive(Debug)]
    pub struct Error;
    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str("date error") }
    }
    impl std::error::Error for Error {}

    pub fn into_io_error(error: Error) -> io::Error { io::Error::other(error) }
}
