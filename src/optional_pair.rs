use std::fmt;

/// An [`InsertOptional`] represents a potentail tuple whose elements are potentail tuples. It is a
/// more ergonomic alternative to `Option<(Option<(L,R)>,Option<(L,R)>)>`, and is most often used
/// as a return value for a map's insert method.
///
/// # Examples
/// ```rust
/// use double_map::optional_pair::InsertOptional;
///
/// let op: InsertOptional<String, String> = InsertOptional::SomeLeft(("Hello".to_string(),
/// "World".to_string()));
///
/// match op {
///     InsertOptional::None => { /*...*/ },
///     InsertOptional::SomeLeft((left, right)) => { /*...*/ },
///     InsertOptional::SomeRight(pair) => { /*...*/ },
///     InsertOptional::SomeBoth(l_pair, r_pair) => { /*...*/ },
///     InsertOptional::SomePair(pair) => { /*...*/ },
/// }
/// ```
#[derive(PartialEq, Eq)]
pub enum InsertOptional<L, R>
where
    L: PartialEq + Eq,
    R: PartialEq + Eq,
{
    None,
    SomePair((L, R)),
    SomeLeft((L, R)),
    SomeRight((L, R)),
    SomeBoth((L, R), (L, R)),
}

impl<L, R> fmt::Debug for InsertOptional<L, R>
where
    L: fmt::Debug + Eq,
    R: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => {
                write!(f, "None")
            }
            Self::SomeLeft(pair) => {
                write!(f, "SomeLeft( {pair:?} )")
            }
            Self::SomeRight(pair) => {
                write!(f, "SomeRight( {pair:?} )")
            }
            Self::SomeBoth(l_pair, r_pair) => {
                write!(f, "SomeBoth( {l_pair:?}, {r_pair:?} )")
            }
            Self::SomePair(pair) => {
                write!(f, "SomePair( {pair:?} )")
            }
        }
    }
}

impl<L, R> From<(Option<(L, R)>, Option<(L, R)>)> for InsertOptional<L, R>
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: (Option<(L, R)>, Option<(L, R)>)) -> Self {
        match input_pair {
            (Some(pair_1), Some(pair_2)) => Self::SomeBoth(pair_1, pair_2),
            (Some(inner_pair), None) => Self::SomeLeft(inner_pair),
            (None, Some(inner_pair)) => Self::SomeRight(inner_pair),
            (None, None) => InsertOptional::None,
        }
    }
}

#[derive(PartialEq, Eq)]
pub enum SwapOptional<I, L, R>
where
    I: PartialEq + Eq,
    L: PartialEq + Eq,
    R: PartialEq + Eq,
{
    None,
    Item(I),
    Collision((L, R)),
    Eq((L, R)),
    ItemAndEq(I, (L, R)),
    ItemAndCollision(I, (L, R)),
    ItemEqAndCollision(I, (L, R), (L, R)),
}

impl<I, L, R> fmt::Debug for SwapOptional<I, L, R>
where
    I: fmt::Debug + Eq,
    L: fmt::Debug + Eq,
    R: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => {
                write!(f, "None")
            }
            Self::Item(item) => {
                write!(f, "Item({item:?})")
            }
            Self::Collision(pair) => {
                write!(f, "Collision({pair:?})")
            }
            Self::Eq(pair) => {
                write!(f, "Eq({pair:?})")
            }
            Self::ItemAndEq(item, pair) => {
                write!(f, "ItemAndEq( {item:?}, {pair:?})")
            }
            Self::ItemAndCollision(item, pair) => {
                write!(f, "ItemAndCollision( {item:?}, {pair:?})")
            }
            Self::ItemEqAndCollision(item, eq_pair, col_pair) => {
                write!(
                    f,
                    "ItemEqAndCollision( {item:?}, {eq_pair:?}, {col_pair:?})"
                )
            }
        }
    }
}

impl<I, L, R> From<(Option<I>, Option<(L, R)>, Option<(L, R)>)> for SwapOptional<I, L, R>
where
    I: Eq,
    L: Eq,
    R: Eq,
{
    fn from(input: (Option<I>, Option<(L, R)>, Option<(L, R)>)) -> Self {
        match input {
            (None, _, _) => Self::None,
            (Some(item), None, None) => Self::Item(item),
            (Some(item), Some(pair), None) => Self::ItemAndEq(item, pair),
            (Some(item), None, Some(pair)) => Self::ItemAndCollision(item, pair),
            (Some(item), Some(eq), Some(col)) => Self::ItemEqAndCollision(item, eq, col),
        }
    }
}
