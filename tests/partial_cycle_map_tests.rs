#[cfg(test)]
mod tests {
    use cycle_map::{OptionalPair, PartialCycleMap};
    use hashbrown::HashSet;
    use OptionalPair::*;

    #[derive(PartialEq, Eq, Clone, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> PartialCycleMap<String, TestingStruct> {
        (0..10)
            .map(|i| (i.to_string(), TestingStruct::from_value(i)))
            .collect()
    }

    fn construct_unpaired_map() -> PartialCycleMap<String, TestingStruct> {
        let mut digest = PartialCycleMap::with_capacity(10);
        for i in 0..10 {
            digest.insert_left(i.to_string());
            digest.insert_right(TestingStruct::from_value(i));
        }
        digest
    }

    #[test]
    fn construction_test() {
        let map: PartialCycleMap<String, TestingStruct> = PartialCycleMap::new();
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
    fn unpaired_construction_test() {
        let map = construct_unpaired_map();
        assert_eq!(map.len_left(), 10);
        assert_eq!(map.len_right(), 10);
    }

    #[test]
    fn insert_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, (Neither, Neither));
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
        let map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        assert!(map.contains_left(&0.to_string()));
        assert!(map.contains_right(&TestingStruct::from_value(0)));
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
        assert_eq!(opt, SomeBoth("0".to_string(), TestingStruct::from_value(0)));
        // Right remove
        let mut map: PartialCycleMap<String, TestingStruct> = construct_default_map();
        let opt = map.remove_via_left(&"42".to_string());
        assert!(opt.is_none());
        let opt = map.remove_via_left(&"0".to_string());
        assert_eq!(opt, SomeBoth("0".to_string(), TestingStruct::from_value(0)));
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
        assert_eq!(opt, SomeLeft("0".to_string()));
        let opt = map.get_right(&"101".to_string());
        assert_eq!(opt, Some(&TestingStruct::from_value(0)));
        // With collision
        let mut map = construct_default_map();
        let opt = map.swap_left(&"0".to_string(), "1".to_string());
        assert_eq!(
            opt,
            SomeBoth(
                "0".to_string(),
                SomeBoth("1".to_string(), TestingStruct::from_value(1))
            )
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
        assert_eq!(opt, Neither);
        let opt = map.swap_left_checked(
            &"0".to_string(),
            &TestingStruct::from_value(0),
            "101".to_string(),
        );
        assert_eq!(opt, SomeLeft("0".to_string()));
    }

    #[test]
    fn swap_left_or_insert_tests() {
        let mut map = construct_default_map();
        let opt = map.swap_left_or_insert(
            &"0".to_string(),
            "101".to_string(),
            TestingStruct::from_value(0),
        );
        assert_eq!(opt, SomeLeft("0".to_string()));
        // No collision
        let mut map = construct_default_map();
        let opt = map.swap_left_or_insert(
            &"101".to_string(),
            "102".to_string(),
            TestingStruct::from_value(102),
        );
        assert_eq!(opt, Neither);
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
        assert_eq!(opt, SomeLeft(TestingStruct::from_value(0)));
        let opt = map.get_left(&TestingStruct::from_value(101));
        assert_eq!(opt, Some(&"0".to_string()));
        // With collision
        let mut map = construct_default_map();
        let opt = map.swap_right(&TestingStruct::from_value(0), TestingStruct::from_value(1));
        assert_eq!(
            opt,
            SomeBoth(
                TestingStruct::from_value(0),
                SomeBoth("1".to_string(), TestingStruct::from_value(1))
            )
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
        assert_eq!(opt, Neither);
        let opt = map.swap_right_checked(
            &TestingStruct::from_value(0),
            &"0".to_string(),
            TestingStruct::from_value(101),
        );
        assert_eq!(opt, SomeLeft(TestingStruct::from_value(0)));
    }

    #[test]
    fn swap_right_or_insert_tests() {
        let mut map = construct_default_map();
        let opt = map.swap_right_or_insert(
            &TestingStruct::from_value(0),
            TestingStruct::from_value(101),
            "0".to_string(),
        );
        assert_eq!(opt, SomeLeft(TestingStruct::from_value(0)));
        let mut map = construct_default_map();
        let opt = map.swap_right_or_insert(
            &TestingStruct::from_value(101),
            TestingStruct::from_value(102),
            "102".to_string(),
        );
        assert_eq!(opt, Neither);
    }

    #[test]
    fn retain_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
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
        map.retain(|x| {
            if let Some(l) = x.get_left() {
                *l % 2 == 0
            } else {
                true
            }
        });
        assert_eq!(map.len_left(), 33);
        assert_eq!(map.len_right(), 50);
        for op in map.iter() {
            match op {
                SomeLeft(val) | SomeBoth(val, _) => {
                    assert_eq!(val % 2, 1);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn retain_mapped_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
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
                    assert_eq!(val % 2, 1);
                }
                _ => {}
            }
        }
    }

    #[test]
    fn retain_unmapped_test() {
        let mut map: PartialCycleMap<u64, String> = PartialCycleMap::with_capacity(100);
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
        assert_eq!(map.len_left(), 50);
        assert_eq!(map.len_right(), 34);
        for op in map.iter() {
            println!("{op:?}");
            match op {
                SomeLeft(val) => {
                    assert_eq!(val % 2, 1);
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
                .collect::<PartialCycleMap<String, TestingStruct>>(),
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
                .collect::<PartialCycleMap<String, TestingStruct>>(),
            map
        );
        let map = construct_unpaired_map();
        let iter = map.iter_mapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.clone().len(), 0);
        assert_eq!(
            iter.map(|(l, r)| (l.clone(), r.clone()))
                .collect::<PartialCycleMap<String, TestingStruct>>(),
            PartialCycleMap::new()
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
                .collect::<PartialCycleMap<String, TestingStruct>>(),
            map
        );
        let map = construct_default_map();
        let iter = map.iter_unmapped();
        println!("{iter:?}");
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.clone().len(), 0);
        assert_eq!(
            iter.map(|op| op.cloned())
                .collect::<PartialCycleMap<String, TestingStruct>>(),
            PartialCycleMap::new()
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
    fn forced_pairing_tests() {
        let mut map = construct_unpaired_map();
        for i in 0..5 {
            assert_eq!(
                map.pair_forced(&i.to_string(), &TestingStruct::from_value(i)),
                Neither
            );
        }
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        for i in 0..5 {
            assert_eq!(
                map.pair_forced(&i.to_string(), &TestingStruct::from_value(i + 5)),
                SomeRight(&TestingStruct::from_value(i))
            );
        }
        assert!((0..5).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        for i in 5..10 {
            assert_eq!(
                map.pair_forced(&i.to_string(), &TestingStruct::from_value(i)),
                SomeLeft(&(i - 5).to_string())
            );
        }
        assert!((0..5).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        assert!((5..10).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        for i in 0..10 {
            map.pair_forced(&i.to_string(), &TestingStruct::from_value(i));
        }
        for i in 0..5 {
            assert_eq!(
                map.pair_forced(&i.to_string(), &TestingStruct::from_value(i + 5)),
                SomeBoth(&(i + 5).to_string(), &TestingStruct::from_value(i))
            );
        }
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        assert!((0..10).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        assert!((5..10).all(|i| !map.is_left_paired(&i.to_string())));
        assert!((0..5).all(|i| !map.is_right_paired(&TestingStruct::from_value(i))));
    }

    #[test]
    fn forced_removed_pairing_tests() {
        let mut map = construct_unpaired_map();
        for i in 0..5 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                Neither
            );
        }
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        for i in 0..5 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i + 5)),
                SomeRight(TestingStruct::from_value(i))
            );
        }
        assert!((0..5).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        for i in 5..10 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                SomeLeft((i - 5).to_string())
            );
        }
        assert!((0..5).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        assert!((5..10).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        println!("New map");
        let mut map = construct_unpaired_map();
        for i in 0..10 {
            map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i));
        }
        for i in 0..5 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i + 5)),
                SomeBoth((i + 5).to_string(), TestingStruct::from_value(i))
            );
        }
        assert!((0..5).all(|i| map.are_mapped(&i.to_string(), &TestingStruct::from_value(i + 5))));
        assert!((0..10).all(|i| !map.are_mapped(&i.to_string(), &TestingStruct::from_value(i))));
        assert!((5..10).all(|i| !map.is_left_paired(&i.to_string())));
        assert!((0..5).all(|i| !map.is_right_paired(&TestingStruct::from_value(i))));
    }

    #[test]
    fn drain_tests() {
        let mut map = construct_unpaired_map();
        let l_cap = map.capacity_left();
        let r_cap = map.capacity_right();
        for i in 0..5 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                Neither
            );
        }
        let other_map: PartialCycleMap<String, TestingStruct> = map.drain().collect();
        let mut new_map = construct_unpaired_map();
        for i in 0..5 {
            assert_eq!(
                new_map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                Neither
            );
        }
        assert_eq!(map.len_left(), 0);
        assert_eq!(map.len_right(), 0);
        assert_eq!(map.capacity_left(), l_cap);
        assert_eq!(map.capacity_right(), r_cap);
        assert_eq!(other_map, new_map);
        let mut map = construct_unpaired_map();
        let l_cap = map.capacity_left();
        let r_cap = map.capacity_right();
        for i in 0..5 {
            assert_eq!(
                map.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                Neither
            );
        }
        let other_map: PartialCycleMap<String, TestingStruct> = map
            .drain_filter(|op| match op.get_right() {
                Some(r) => r.value % 2 == 0,
                None => false,
            })
            .collect();
        let mut new_map_one = construct_unpaired_map();
        for i in 0..10 {
            if i % 2 == 0 {
                new_map_one.remove_via_right(&TestingStruct::from_value(i));
            } else if i < 5 {
                assert_eq!(
                    new_map_one.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                    Neither
                );
            }
        }
        let mut new_map_two = construct_unpaired_map();
        for i in 0..10 {
            if i % 2 == 1 {
                new_map_two.remove_via_right(&TestingStruct::from_value(i));
            } else if i < 5 {
                assert_eq!(
                    new_map_two.pair_forced_remove(&i.to_string(), &TestingStruct::from_value(i)),
                    Neither
                );
            }
        }
        assert_eq!(map.len_left(), 7);
        assert_eq!(map.len_right(), 5);
        assert_eq!(map.capacity_left(), l_cap);
        assert_eq!(map.capacity_right(), r_cap);
        assert_eq!(map, new_map_one);
        assert_eq!(other_map, new_map_two);
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
