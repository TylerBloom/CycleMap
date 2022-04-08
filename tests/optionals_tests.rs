#[cfg(test)]
mod tests {
    use cycle_map::OptionalPair;

    #[test]
    fn is_tests() {
        let op: OptionalPair<&str, u64> = OptionalPair::SomeLeft("hello");
        assert!(op.is_some());
    }

    #[test]
    fn convert_test() {
        let op_1: OptionalPair<&str, &str> = OptionalPair::SomeLeft("hello");
        let op_2: OptionalPair<String, String> = op_1.convert();
        assert_eq!(op_2, OptionalPair::SomeLeft(String::from("hello")));
    }

    #[test]
    fn map_tests() {
        let no: OptionalPair<u64, u64> = OptionalPair::None;
        let sl: OptionalPair<u64, u64> = OptionalPair::SomeLeft(42);
        let sr: OptionalPair<u64, u64> = OptionalPair::SomeRight(84);
        let sb: OptionalPair<u64, u64> = OptionalPair::SomeBoth(42, 84);
        // Map tests
        assert_eq!(
            no.clone().map(|l| l.to_string(), |r| r.to_string()),
            OptionalPair::None
        );
        assert_eq!(
            sl.clone().map(|l| l.to_string(), |r| r.to_string()),
            OptionalPair::SomeLeft(String::from("42"))
        );
        assert_eq!(
            sr.clone().map(|l| l.to_string(), |r| r.to_string()),
            OptionalPair::SomeRight(String::from("84"))
        );
        assert_eq!(
            sb.clone().map(|l| l.to_string(), |r| r.to_string()),
            OptionalPair::SomeBoth(String::from("42"), String::from("84"))
        );
        // Map left tests
        assert_eq!(no.clone().map_left(|l| l.to_string()), OptionalPair::None);
        assert_eq!(
            sl.clone().map_left(|l| l.to_string()),
            OptionalPair::SomeLeft(String::from("42"))
        );
        assert_eq!(
            sr.clone().map_left(|l| l.to_string()),
            OptionalPair::SomeRight(84)
        );
        assert_eq!(
            sb.clone().map_left(|l| l.to_string()),
            OptionalPair::SomeBoth(String::from("42"), 84)
        );
        // Map right tests
        assert_eq!(no.clone().map_right(|r| r.to_string()), OptionalPair::None);
        assert_eq!(
            sl.clone().map_right(|r| r.to_string()),
            OptionalPair::SomeLeft(42)
        );
        assert_eq!(
            sr.clone().map_right(|r| r.to_string()),
            OptionalPair::SomeRight(String::from("84"))
        );
        assert_eq!(
            sb.clone().map_right(|r| r.to_string()),
            OptionalPair::SomeBoth(42, String::from("84"))
        );
    }

    #[test]
    fn from_tests() {
        // None tests
        let no: OptionalPair<u64, u64> = OptionalPair::None;
        let no_opt: Option<(Option<u64>, Option<u64>)> = no.clone().into();
        assert_eq!(no, OptionalPair::from(no_opt));
        let no_tup: (Option<u64>, Option<u64>) = no.clone().into();
        assert_eq!(no, OptionalPair::from(no_tup));
        // SomeLeft tests
        let sl: OptionalPair<u64, u64> = OptionalPair::SomeLeft(42);
        let sl_opt: Option<(Option<u64>, Option<u64>)> = sl.clone().into();
        assert_eq!(sl, OptionalPair::from(sl_opt));
        let sl_tup: (Option<u64>, Option<u64>) = sl.clone().into();
        assert_eq!(sl, OptionalPair::from(sl_tup));
        // SomeRight tests
        let sr: OptionalPair<u64, u64> = OptionalPair::SomeRight(84);
        let sr_opt: Option<(Option<u64>, Option<u64>)> = sr.clone().into();
        assert_eq!(sr, OptionalPair::from(sr_opt));
        let sr_tup: (Option<u64>, Option<u64>) = sr.clone().into();
        assert_eq!(sr, OptionalPair::from(sr_tup));
        // SomeBoth tests
        let sb: OptionalPair<u64, u64> = OptionalPair::SomeBoth(42, 84);
        let sb_opt: Option<(Option<u64>, Option<u64>)> = sb.clone().into();
        assert_eq!(sb, OptionalPair::from(sb_opt));
        let sb_tup: (Option<u64>, Option<u64>) = sb.clone().into();
        assert_eq!(sb, OptionalPair::from(sb_tup));
    }
}
