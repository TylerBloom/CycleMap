#[cfg(test)]
mod tests {
    use cycle_map::MultiCycleMap;
    use hashbrown::HashSet;

    #[derive(PartialEq, Eq, Clone, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> MultiCycleMap<String, TestingStruct> {
        (0..10)
            .map(|i| (i.to_string(), TestingStruct::from_value(i)))
            .collect()
    }

    #[test]
    fn construction_test() {
        let map: MultiCycleMap<String, TestingStruct> = MultiCycleMap::new();
        assert_eq!(map.len_left(), 0);
        assert_eq!(map.len_right(), 0);
        assert_eq!(map.capacity_left(), 0);
        assert_eq!(map.capacity_right(), 0);
        let mut map = construct_default_map();
        assert_eq!(map.len_left(), 10);
        assert_eq!(map.len_right(), 10);
        let l_cap = map.capacity_left();
        let r_cap = map.capacity_right();
        map.clear();
        assert!(map.is_empty());
        assert_eq!(map.len_left(), 0);
        assert_eq!(map.len_right(), 0);
        assert_eq!(map.capacity_left(), l_cap);
        assert_eq!(map.capacity_right(), r_cap);
    }

    #[test]
    fn insert_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, (None, None));
        }
        assert_eq!(map.len_left(), 100);
        assert_eq!(map.len_right(), 100);
        for (val, s) in map.iter_mapped() {
            assert_eq!(val.to_string(), *s);
            assert_eq!(str::parse::<u64>(s).expect("Unreachable"), *val);
            println!("{val}, {s}");
        }
    }

    #[test]
    fn get_tests() {
        let map: MultiCycleMap<String, TestingStruct> = construct_default_map();
        assert!(map.contains_left(&0.to_string()));
        assert!(map.contains_right(&TestingStruct::from_value(0)));
        let opt = map.get_left_iter(&TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.get_left_iter(&TestingStruct::from_value(0));
        assert!(opt.is_some());
        assert_eq!(Some(&"0".to_string()), opt.unwrap().next());
        let opt = map.get_right(&"42".to_string());
        assert!(opt.is_none());
        let opt = map.get_right(&"0".to_string());
        assert_eq!(opt, Some(&TestingStruct::from_value(0)));
    }

    #[test]
    fn remove_tests() {
        // Double remove
        let mut map: MultiCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove(&"42".to_string(), &TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.remove(&"0".to_string(), &TestingStruct::from_value(0));
        assert_eq!(
            opt,
            Some((vec!["0".to_string()], TestingStruct::from_value(0)))
        );
        // Left remove
        let mut map: MultiCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_right(&TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.remove_via_right(&TestingStruct::from_value(0));
        assert_eq!(
            opt,
            Some((vec!["0".to_string()], TestingStruct::from_value(0)))
        );
        // Right remove
        let mut map: MultiCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_left(&"42".to_string());
        assert!(opt.is_none());
        let opt = map.remove_via_left(&"0".to_string());
        assert_eq!(opt, Some("0".to_string()));
    }

    #[test]
    fn retain_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            if i < 50 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (None, None));
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, None);
            }
        }
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 100);
        map.retain(|opt, _| opt.is_none() );
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 50);
    }

    #[test]
    fn retain_mapped_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            if i < 50 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (None, None));
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, None);
            }
        }
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 100);
        map.retain_mapped(|l, _| *l % 2 == 0);
        assert_eq!(map.len_left(), 25);
        assert_eq!(map.len_right(), 75);
        for op in map.iter() {
            println!("{op:?}");
            if let Some(x) = op.0 {
                assert_eq!(x % 2, 1);
            }
        }
    }

    #[test]
    fn retain_unmapped_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            if i < 50 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (None, None));
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, None);
            }
        }
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 100);
        map.retain_unmapped(|val| val.parse::<u64>().unwrap() % 2 == 0);
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 75);
    }

    #[test]
    fn iter_tests() {
        // Main iter
        let map = construct_default_map();
        let iter = map.iter();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        // Left iter
        let map = construct_default_map();
        let iter = map.iter_left();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        assert_eq!(
            iter.cloned().collect::<HashSet<String>>(),
            (0..10).map(|i| i.to_string()).collect::<HashSet<String>>()
        );
        // Right iter
        let map = construct_default_map();
        let iter = map.iter_right();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        assert_eq!(
            iter.cloned().collect::<HashSet<TestingStruct>>(),
            (0..10)
                .map(|i| TestingStruct::from_value(i))
                .collect::<HashSet<TestingStruct>>()
        );
    }

    #[test]
    fn mapped_iter_tests() {
        // Mapped iter
        let map = construct_default_map();
        let iter = map.iter_mapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        assert_eq!(
            iter.map(|(l, r)| (l.clone(), r.clone()))
                .collect::<MultiCycleMap<String, TestingStruct>>(),
            map
        );
        let map: MultiCycleMap<String, TestingStruct> = (0..10)
            .map(|i| (None, TestingStruct::from_value(i)))
            .collect();
        let iter = map.iter_mapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.clone().len(), 0);
        assert_eq!(
            iter.map(|(l, r)| (l.clone(), r.clone()))
                .collect::<MultiCycleMap<String, TestingStruct>>(),
            MultiCycleMap::new()
        );
    }

    #[test]
    fn unmapped_iter_tests() {
        // Unmapped iter
        let map: MultiCycleMap<String, TestingStruct> = (0..10)
            .map(|i| (None, TestingStruct::from_value(i)))
            .collect();
        let iter = map.iter_unmapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        let map = construct_default_map();
        let iter = map.iter_unmapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.clone().len(), 0);
    }

    #[test]
    fn pairing_tests() {
        let mut map: MultiCycleMap<String, TestingStruct> = (0..10)
            .map(|i| (None, TestingStruct::from_value(i)))
            .collect();
        for i in 0..5 {
            assert_eq!(
                map.insert_left(i.to_string(), &TestingStruct::from_value(i)),
                None
            );
        }
        for i in 0..5 {
            assert!(map.pair(&i.to_string(), &TestingStruct::from_value(i + 5)));
            assert!(map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5)));
            assert!(!map.are_mapped(&i.to_string(), &TestingStruct::from_value(i)));
        }
        for i in 0..10 {
            if i < 5 {
                assert!(map.are_mapped(&i.to_string(), &TestingStruct::from_value(i+5)));
                assert!(!map.are_mapped(&i.to_string(), &TestingStruct::from_value(i)));
            } else {
                assert!(!map.are_mapped(&i.to_string(), &TestingStruct::from_value(i)));
                assert!(map.are_mapped(&(i-5).to_string(), &TestingStruct::from_value(i)));
            }
        }
    }

    #[test]
    fn misc_tests() {
        let map = construct_default_map();
        assert!(!map.are_mapped(&"0".to_string(), &TestingStruct::from_value(1)));
    }

    #[test]
    fn eq_test() {
        let map = construct_default_map();
        assert_eq!(map.clone(), construct_default_map());
        assert_eq!(construct_default_map(), construct_default_map());
    }

    #[test]
    fn fmt_tests() {
        let map = construct_default_map();
        println!("{map:?}");
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
