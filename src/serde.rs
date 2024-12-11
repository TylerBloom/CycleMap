use crate::CycleMap;
use core::{
    fmt,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};
use serde::{
    de::{SeqAccess, Visitor},
    ser::{SerializeSeq, Serializer},
    Deserializer, {Deserialize, Serialize},
};

pub(crate) struct CycleMapVisitor<L, R, S> {
    marker: PhantomData<fn() -> CycleMap<L, R, S>>,
}

impl<L, R, S> CycleMapVisitor<L, R, S>
where
    L: Eq + Hash,
    R: Eq + Hash,
    S: BuildHasher + Clone,
{
    fn new() -> Self {
        CycleMapVisitor {
            marker: PhantomData,
        }
    }
}

impl<'de, L, R, S> Visitor<'de> for CycleMapVisitor<L, R, S>
where
    L: Deserialize<'de> + Eq + Hash,
    R: Deserialize<'de> + Eq + Hash,
    S: BuildHasher + Clone + Default,
{
    type Value = CycleMap<L, R, S>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a CycleMap")
    }

    fn visit_seq<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: SeqAccess<'de>,
    {
        let mut map: CycleMap<L, R, S> =
            CycleMap::with_capacity_and_hasher(access.size_hint().unwrap_or(0), Default::default());

        while let Some(entry) = access.next_element::<(L, R)>()? {
            map.insert(entry.0, entry.1);
        }

        Ok(map)
    }
}

impl<'de, L, R, S> Deserialize<'de> for CycleMap<L, R, S>
where
    L: Deserialize<'de> + Eq + Hash,
    R: Deserialize<'de> + Eq + Hash,
    S: BuildHasher + Clone + Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(CycleMapVisitor::<L, R, S>::new())
    }
}

impl<L, R, H> Serialize for CycleMap<L, R, H>
where
    L: Serialize + Eq + Hash,
    R: Serialize + Eq + Hash,
    H: BuildHasher + Clone,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_seq(Some(self.len()))?;

        for pair in self.iter() {
            map.serialize_element(&pair)?;
        }

        map.end()
    }
}

#[cfg(test)]
mod tests {
    use crate::CycleMap;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, PartialEq, Eq, Clone, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> CycleMap<String, TestingStruct> {
        (0..10)
            .map(|i| (i.to_string(), TestingStruct::from_value(i)))
            .collect()
    }

    #[test]
    fn serialize_deserialize_test() {
        let map = construct_default_map();
        let jsonified: String =
            serde_json::to_string(&map).expect("Unable to convert data to json!");
        println!("JSON: {jsonified}");
        let reconsituted: CycleMap<String, TestingStruct> =
            serde_json::from_str(&jsonified).expect("Unable to convert json to hashbag!");
        println!("From json: {reconsituted:?}");
        assert_eq!(map, reconsituted);
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
