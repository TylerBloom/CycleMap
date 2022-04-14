#[cfg(test)]
mod tests {
    use cycle_map::{OptionalPair, MultiCycleMap};
    use hashbrown::HashSet;
    use OptionalPair::*;

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
        assert_eq!(opt, Some((vec!["0".to_string()], TestingStruct::from_value(0))));
        // Left remove
        let mut map: MultiCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_right(&TestingStruct::from_value(42));
        assert!(opt.is_none());
        let opt = map.remove_via_right(&TestingStruct::from_value(0));
        assert_eq!(opt, Some((vec!["0".to_string()], TestingStruct::from_value(0))));
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
            if i < 34 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (None, None));
            } else if i < 67 {
                let opt = map.insert_left(i, &i.to_string());
                assert_eq!(opt, None);
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, None);
            }
        }
        assert_eq!(map.len_left(), 67);
        assert_eq!(map.len_right(), 67);
        map.retain(|opt,_| {
            match opt {
                Some(x) => x % 2 == 0,
                None => true,
            }
        });
        assert_eq!(map.len_left(), 34);
        assert_eq!(map.len_right(), 50);
        for opt in map.iter() {
            match opt {
                SomeLeft(val) | SomeBoth(val, _) => {
                    assert_eq!(val % 2, 0);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn retain_mapped_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            if i < 34 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (Neither, Neither));
            } else if i < 67 {
                let opt = map.insert_left(i);
                assert_eq!(opt, Neither);
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, Neither);
            }
        }
        assert_eq!(map.len_left(), 67);
        assert_eq!(map.len_right(), 67);
        map.retain_mapped(|l, _| *l % 2 == 0);
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 50);
        for op in map.iter() {
            println!("{op:?}");
            match op {
                SomeBoth(val, _) => {
                    assert_eq!(val % 2, 0);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn retain_unmapped_test() {
        let mut map: MultiCycleMap<u64, String> = MultiCycleMap::with_capacity(100);
        for i in 0..100 {
            if i < 34 {
                let opt = map.insert(i, i.to_string());
                assert_eq!(opt, (Neither, Neither));
            } else if i < 67 {
                let opt = map.insert_left(i);
                assert_eq!(opt, Neither);
            } else {
                let opt = map.insert_right(i.to_string());
                assert_eq!(opt, Neither);
            }
        }
        assert_eq!(map.len_left(), 67);
        assert_eq!(map.len_right(), 67);
        map.retain_unmapped(|op| {
            if let Some(l) = op.get_left() {
                *l % 2 == 0
            } else {
                true
            }
        });
        assert_eq!(map.len_left(), 51);
        assert_eq!(map.len_right(), 67);
        for op in map.iter() {
            println!("{op:?}");
            match op {
                SomeLeft(val) => {
                    assert_eq!(val % 2, 0);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn iter_tests() {
        // Main iter
        let map = construct_default_map();
        let iter = map.iter();
        println!("{iter:?}");
        assert_eq!(iter.len(), 10);
        assert_eq!(iter.clone().len(), 10);
        assert_eq!(
            iter.map(|op| op.cloned())
                .collect::<MultiCycleMap<String, TestingStruct>>(),
            map
        );
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
        let map = construct_unpaired_map();
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
        let map = construct_unpaired_map();
        let iter = map.iter_unmapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 20);
        assert_eq!(iter.clone().len(), 20);
        assert_eq!(
            iter.map(|op| op.cloned())
                .collect::<MultiCycleMap<String, TestingStruct>>(),
            map
        );
        let map = construct_default_map();
        let iter = map.iter_unmapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.clone().len(), 0);
        assert_eq!(
            iter.map(|op| op.cloned())
                .collect::<MultiCycleMap<String, TestingStruct>>(),
            MultiCycleMap::new()
        );
    }

    #[test]
    fn pairing_tests() {
        let mut map = construct_unpaired_map();
        for i in 0..5 {
            assert!(map.pair(&i.to_string(), &TestingStruct::from_value(i)));
        }
        for i in 0..5 {
            assert!(!map.pair(&i.to_string(), &TestingStruct::from_value(i + 5)));
        }
        for i in 0..10 {
            if i < 5 {
                assert!(map.are_mapped(&i.to_string(), &TestingStruct::from_value(i)));
            } else {
                assert!(!map.are_mapped(&i.to_string(), &TestingStruct::from_value(i)));
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
