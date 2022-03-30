use std::fmt;

/// An [`OptionalPair`] represents a potentail tuple whose elements are potentail tuples. It is a
/// more ergonomic alternative to `Option<(Option<(L,R)>,Option<(L,R)>)>`, and is most often used
/// as a return value for a map's insert method.
///
/// # Examples
/// ```rust
/// use double_map::optional_pair::OptionalPair;
///
/// let op: OptionalPair<String, String> = OptionalPair::SomeLeft(("Hello".to_string(),
/// "World".to_string()));
///
/// match op {
///     OptionalPair::None => { /*...*/ },
///     OptionalPair::SomeLeft((left, right)) => { /*...*/ },
///     OptionalPair::SomeRight((left, right)) => { /*...*/ },
///     OptionalPair::SomeBoth((l_pair, r_pair)) => { /*...*/ },
///     OptionalPair::SomePair(pair) => { /*...*/ },
/// }
/// ```
#[derive(PartialEq, Eq)]
pub enum OptionalPair<L, R>
where
    L: PartialEq + Eq,
    R: PartialEq + Eq,
{
    None,
    SomePair((L, R)),
    SomeLeft((L, R)),
    SomeRight((L, R)),
    SomeBoth(((L, R), (L, R))),
}

impl<L, R> fmt::Debug for OptionalPair<L, R>
where
    L: fmt::Debug + Eq,
    R: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => { write!(f, "None") },
            Self::SomeLeft(pair) => { write!(f, "( ({:?}), None )", pair) },
            Self::SomeRight(pair) => { write!(f, "( None, ({:?}) )", pair) },
            Self::SomeBoth((l_pair, r_pair)) => { write!(f, "( ({:?}), ({:?}) )", l_pair, r_pair) },
            Self::SomePair(pair) => { write!(f, "{:?}", pair) },
        }
    }
}

impl<L, R> From<(Option<(L, R)>, Option<(L, R)>)> for OptionalPair<L, R>
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: (Option<(L, R)>, Option<(L, R)>)) -> Self {
        match input_pair {
            (Some(pair_1), Some(pair_2)) => Self::SomeBoth((pair_1, pair_2)),
            (Some(inner_pair), None) => Self::SomeLeft(inner_pair),
            (None, Some(inner_pair)) => Self::SomeRight(inner_pair),
            (None, None) => OptionalPair::None,
        }
    }
}
