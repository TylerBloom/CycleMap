#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use cycle_map::{cycle_map::CycleMap, optional_pair::*};

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
    fn insert_test() {
        let mut map: CycleMap<u64, String> = CycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, InsertOptional::None);
        }
        assert_eq!(map.len(), 100);
        for (val, s) in map.iter() {
            assert_eq!(val.to_string(), *s);
            assert_eq!(str::parse::<u64>(s).expect("Unreachable"), *val);
            println!("{val}, {s}");
        }
    }

    #[test]
    fn collision_test() {
        let mut map: CycleMap<String, BumpingStruct> = CycleMap::with_capacity(3);
        let opt = map.insert(
            "one".to_string(),
            BumpingStruct {
                hashable: "one".to_string(),
                value: "one".to_string(),
            },
        );
        assert_eq!(opt, InsertOptional::None);
        assert_eq!(map.len(), 1);
        let opt = map.insert(
            "two".to_string(),
            BumpingStruct {
                hashable: "two".to_string(),
                value: "two".to_string(),
            },
        );
        assert_eq!(opt, InsertOptional::None);
        assert_eq!(map.len(), 2);
        let opt = map.insert(
            "two".to_string(),
            BumpingStruct {
                hashable: "two".to_string(),
                value: "three".to_string(),
            },
        );
        assert_eq!(
            opt,
            InsertOptional::SomePair((
                "two".to_string(),
                BumpingStruct {
                    hashable: "two".to_string(),
                    value: "two".to_string(),
                }
            ))
        );
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn get_tests() {}

    #[test]
    fn remove_tests() {}

    #[test]
    fn swap_tests() {}

    #[test]
    fn retain_test() {
        let mut map: CycleMap<u64, String> = CycleMap::with_capacity(100);
        for i in 0..100 {
            let opt = map.insert(i, i.to_string());
            assert_eq!(opt, InsertOptional::None);
        }
        assert_eq!(map.len(), 100);
        map.retain(|x, _| x % 2 == 0);
        assert_eq!(map.len(), 50);
        for (val, s) in map.iter() {
            assert_eq!(val % 2, 0);
            println!("{val}, {s}");
        }
    }
}
