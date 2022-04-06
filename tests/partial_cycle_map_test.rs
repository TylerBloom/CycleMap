#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use cycle_map::{OptionalPair, PartialCycleMap};

    #[derive(PartialEq, Eq, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> PartialCycleMap<String, TestingStruct> {
        (0..10)
            .map(|i| (i.to_string(), TestingStruct::from_value(i)))
            .collect()
    }

    #[derive(PartialEq, Eq, Debug)]
    struct BumpingStruct {
        hashable: String,
        value: String,
    }

    impl Hash for BumpingStruct {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.hashable.hash(state)
        }
    }

    #[test]
    fn construction_test() {
        let map: PartialCycleMap<String, TestingStruct> = PartialCycleMap::new();
        assert_eq!(map.len(), 0);
        assert_eq!(map.capacity(), 0);
        let mut map = construct_default_map();
        assert_eq!(map.len(), 10);
        let cap = map.capacity();
        map.clear();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.capacity(), cap);
    }

    #[test]
    fn insert_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, (OptionalPair::None, OptionalPair::None));
        }
        assert_eq!(map.len(), 100);
        for (val, s) in map.iter() {
            assert_eq!(val.to_string(), *s);
            assert_eq!(str::parse::<u64>(s).expect("Unreachable"), *val);
            println!("{val}, {s}");
        }
    }

    #[test]
    fn get_tests() {
        let map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.get_left(&TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.get_left(&TestingStruct::from_value(0));
        assert_eq!(opt, Some(&"0".to_string()));
        let opt = map.get_right(&"42".to_string());
        assert!(opt.is_none());
        let opt = map.get_right(&"0".to_string());
        assert_eq!(opt, Some(&TestingStruct::from_value(0)));
    }

    #[test]
    fn remove_tests() {
        // Double remove
        let mut map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove(&"42".to_string(), &TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.remove(&"0".to_string(), &TestingStruct::from_value(0));
        assert_eq!(opt, Some(("0".to_string(), TestingStruct::from_value(0))));
        // Left remove
        let mut map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_right(&TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.remove_via_right(&TestingStruct::from_value(0));
        assert_eq!(
            opt,
            OptionalPair::SomeBoth("0".to_string(), TestingStruct::from_value(0))
        );
        // Right remove
        let mut map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_left(&"42".to_string());
        assert!(opt.is_none());
        let opt = map.remove_via_left(&"0".to_string());
        assert_eq!(
            opt,
            OptionalPair::SomeBoth("0".to_string(), TestingStruct::from_value(0))
        );
    }

    #[test]
    fn swap_left_not_found_test() {
        // Not Found
        let mut map = construct_default_map();
        let opt = map.swap_left(&"101".to_string(), "102".to_string());
        assert!(opt.is_none());
        // No collision
        let mut map = construct_default_map();
        let opt = map.swap_left(&"0".to_string(), "101".to_string());
        assert_eq!(opt, Some(("0".to_string(), OptionalPair::None)));
        let opt = map.get_right(&"101".to_string());
        assert_eq!(opt, Some(&TestingStruct::from_value(0)));
        // With collision
        let mut map = construct_default_map();
        let opt = map.swap_left(&"0".to_string(), "1".to_string());
        assert_eq!(
            opt,
            Some((
                "0".to_string(),
                OptionalPair::SomeBoth("1".to_string(), TestingStruct::from_value(1))
            ))
        );
        let opt = map.get_right(&"1".to_string());
        assert_eq!(opt, Some(&TestingStruct::from_value(0)));
    }

    #[test]
    fn swap_left_checked_test() {
        let mut map = construct_default_map();
        let opt = map.swap_left_checked(
            &"0".to_string(),
            &TestingStruct::from_value(1),
            "2".to_string(),
        );
        assert_eq!(opt, None);
        let opt = map.swap_left_checked(
            &"0".to_string(),
            &TestingStruct::from_value(0),
            "101".to_string(),
        );
        assert_eq!(opt, Some(("0".to_string(), OptionalPair::None)));
    }

    #[test]
    fn swap_left_or_insert_tests() {
        let mut map = construct_default_map();
        let opt = map.swap_left_or_insert(
            &"0".to_string(),
            "101".to_string(),
            TestingStruct::from_value(0),
        );
        assert_eq!(opt, OptionalPair::SomeLeft("0".to_string()));
        // No collision
        let mut map = construct_default_map();
        let opt = map.swap_left_or_insert(
            &"101".to_string(),
            "102".to_string(),
            TestingStruct::from_value(102),
        );
        assert_eq!(opt, OptionalPair::None);
    }

    #[test]
    fn swap_right_not_found_test() {
        // Not Found
        let mut map = construct_default_map();
        let opt = map.swap_right(
            &TestingStruct::from_value(101),
            TestingStruct::from_value(102),
        );
        assert!(opt.is_none());
        // No collision
        let mut map = construct_default_map();
        let opt = map.swap_right(
            &TestingStruct::from_value(0),
            TestingStruct::from_value(101),
        );
        assert_eq!(
            opt,
            Some((TestingStruct::from_value(0), OptionalPair::None))
        );
        let opt = map.get_left(&TestingStruct::from_value(101));
        assert_eq!(opt, Some(&"0".to_string()));
        // With collision
        let mut map = construct_default_map();
        let opt = map.swap_right(&TestingStruct::from_value(0), TestingStruct::from_value(1));
        assert_eq!(
            opt,
            Some((
                TestingStruct::from_value(0),
                OptionalPair::SomeBoth("1".to_string(), TestingStruct::from_value(1))
            ))
        );
        let opt = map.get_left(&TestingStruct::from_value(1));
        assert_eq!(opt, Some(&"0".to_string()));
    }

    #[test]
    fn swap_right_checked_test() {
        let mut map = construct_default_map();
        let opt = map.swap_right_checked(
            &TestingStruct::from_value(1),
            &"0".to_string(),
            TestingStruct::from_value(2),
        );
        assert_eq!(opt, None);
        let opt = map.swap_right_checked(
            &TestingStruct::from_value(0),
            &"0".to_string(),
            TestingStruct::from_value(101),
        );
        assert_eq!(
            opt,
            Some((TestingStruct::from_value(0), OptionalPair::None))
        );
    }

    #[test]
    fn swap_right_or_insert_tests() {
        let mut map = construct_default_map();
        let opt = map.swap_right_or_insert(
            &TestingStruct::from_value(0),
            TestingStruct::from_value(101),
            "0".to_string(),
        );
        assert_eq!(opt, OptionalPair::SomeLeft(TestingStruct::from_value(0)));
        let mut map = construct_default_map();
        let opt = map.swap_right_or_insert(
            &TestingStruct::from_value(101),
            TestingStruct::from_value(102),
            "102".to_string(),
        );
        assert_eq!(opt, OptionalPair::None);
    }

    #[test]
    fn retain_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, (OptionalPair::None, OptionalPair::None));
        }
        assert_eq!(map.len(), 100);
        map.retain(|x, _| x % 2 == 0);
        assert_eq!(map.len(), 50);
        for (val, s) in map.iter() {
            assert_eq!(val % 2, 0);
            println!("{val}, {s}");
        }
    }

    #[test]
    fn misc_tests() {
        let map = construct_default_map();
        assert!(!map.are_mapped(&"0".to_string(), &TestingStruct::from_value(1)));
    }

    impl TestingStruct {
        pub(crate) fn from_value(value: u64) -> Self {
            Self {
                value,
                data: value.to_string(),
            }
        }
    }
}
