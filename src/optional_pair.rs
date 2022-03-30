/// An [`OptionalPair`] represents a potentail tuple whose elements are potentail tuples. It is a
/// more ergonomic alternative to `Option<(Option<(L,R)>,Option<(L,R)>)>`, and is most often used
/// as a return value for a map's insert method.
///
/// # Examples
/// ```
/// let op: OptionalPair<String, String> = OptionalPair::SomeLeft("Hello".to_string(),
/// "World".to_string());
///
/// match op {
///     None => { ... },
///     SomeLeft(left, right) => { ... },
///     SomeRight(left, right) => { ... },
///     SomeBoth(l_pair, r_pair) => { ... },
///     SinglePair(pair) => { ... },
/// }
/// ```
pub enum OptionalPair<L, R> {
    None,
    SomePair((L, R)),
    SomeLeft((L, R)),
    SomeRight((L, R)),
    SomeBoth(((L, R), (L, R))),
}

impl<L, R> From<(Option<(L, R)>, Option<(L, R)>)> for OptionalPair<L, R> {
    fn from(input_pair: (Option<(L, R)>, Option<(L, R)>)) -> Self {
        match input_pair {
            (Some(pair_1), Some(pair_2)) => Self::SomeBoth((pair_1, pair_2)),
            (Some(inner_pair), None) => Self::SomeLeft(inner_pair),
            (None, Some(inner_pair)) => Self::SomeRight(inner_pair),
            (None, None) => OptionalPair::None,
        }
    }
}
