#![forbid(unsafe_code)]

#[cfg(feature = "model-eq")]
mod eq_model {
    #[cfg(creusot)]
    use creusot_std::prelude::{DeepModel, Int, PartialEq, ensures, logic, pearlite};

    #[derive(Clone, Copy)]
    #[cfg_attr(creusot, derive(creusot_std::std::cmp::PartialEq))]
    #[cfg_attr(not(creusot), derive(PartialEq))]
    pub struct Date { year: u16, month: u8, day: u8 }

    impl Date {
        pub fn new(year: u16, month: u8, day: u8) -> Self { Self { year, month, day } }
    }

    #[cfg(creusot)]
    pub struct DateModel { pub year: Int, pub month: Int, pub day: Int }

    #[cfg(creusot)]
    impl DeepModel for Date {
        type DeepModelTy = DateModel;
        #[logic(open(self))]
        fn deep_model(self) -> DateModel {
            pearlite! { DateModel { year: self.year@, month: self.month@, day: self.day@ } }
        }
    }

    #[cfg_attr(creusot, ensures(result == (a.deep_model() == b.deep_model())))]
    pub fn structural_eq(a: Date, b: Date) -> bool { a == b }

    #[cfg(test)]
    mod tests {
        use super::Date;
        #[test]
        fn native_structural_equality_uses_every_field() {
            let d = Date::new(2024, 2, 29);
            assert!(d == Date::new(2024, 2, 29));
            assert!(d != Date::new(2024, 2, 28));
            assert!(d != Date::new(2024, 3, 29));
            assert!(d != Date::new(2023, 2, 29));
        }
    }
}

#[cfg(feature = "model-ord")]
mod ord_model {
    #[cfg(creusot)]
    use creusot_std::{
        logic::{OrdLogic, PartialOrdLogic, Seq, ord::partial_ord_laws_impl},
        prelude::{DeepModel, Int, PartialEq, ensures, logic, pearlite},
    };
    use core::cmp::Ordering;

    #[derive(Clone, Copy)]
    #[cfg_attr(creusot, derive(creusot_std::std::cmp::PartialEq))]
    #[cfg_attr(not(creusot), derive(PartialEq))]
    pub struct Date { year: u16, month: u8, day: u8 }

    impl Date {
        pub fn new(year: u16, month: u8, day: u8) -> Self { Self { year, month, day } }
    }

    #[cfg(creusot)]
    pub struct DateModel { pub year: Int, pub month: Int, pub day: Int }

    #[cfg(creusot)]
    impl DeepModel for Date {
        type DeepModelTy = DateModel;
        #[logic(open(self))]
        fn deep_model(self) -> DateModel {
            pearlite! { DateModel { year: self.year@, month: self.month@, day: self.day@ } }
        }
    }

    #[cfg(creusot)]
    #[logic(open(self))]
    pub fn lex_key(d: DateModel) -> Seq<Int> {
        Seq::empty().push_back(d.year).push_back(d.month).push_back(d.day)
    }

    #[cfg(creusot)]
    impl PartialOrdLogic for DateModel {
        #[logic(open)]
        fn lt_log(self, other: Self) -> bool {
            lex_key(self).lt_log(lex_key(other))
        }
        partial_ord_laws_impl! {}
    }

    #[cfg(creusot)]
    impl OrdLogic for DateModel {
        #[logic(law)]
        #[ensures(self < other || self == other || other < self)]
        fn lt_log_total(self, other: Self) {
            lex_key(self).lt_log_total(lex_key(other));
        }
    }

    impl Eq for Date {}

    impl PartialOrd for Date {
        #[cfg_attr(creusot, ensures(
            result == self.deep_model().partial_cmp_log(other.deep_model())
        ))]
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for Date {
        #[cfg_attr(creusot, ensures(
            result == self.deep_model().cmp_log(other.deep_model())
        ))]
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

    #[cfg_attr(creusot, ensures(
        result == a.deep_model().cmp_log(b.deep_model())
    ))]
    pub fn chronological_cmp(a: Date, b: Date) -> Ordering { a.cmp(&b) }

    #[cfg(test)]
    mod tests {
        use super::Date;
        use core::cmp::Ordering;
        #[test]
        fn native_lexicographic_order_matches_year_month_day() {
            assert_eq!(Date::new(2024, 2, 28).cmp(&Date::new(2024, 2, 29)), Ordering::Less);
            assert_eq!(Date::new(2024, 2, 29).cmp(&Date::new(2024, 3, 1)), Ordering::Less);
            assert_eq!(Date::new(2023, 12, 31).cmp(&Date::new(2024, 1, 1)), Ordering::Less);
            assert_eq!(Date::new(2024, 2, 29).cmp(&Date::new(2024, 2, 29)), Ordering::Equal);
            assert_eq!(Date::new(2025, 1, 1).cmp(&Date::new(2024, 12, 31)), Ordering::Greater);
        }
    }
}
