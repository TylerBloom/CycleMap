use std::fmt;

/// An OptionalPair represents a potentail tuple whose elements are potentail tuples. It is a
/// more ergonomic alternative to `Option<(Option<(L,R)>,Option<(L,R)>)>`, and is most often used
/// as a return value for a map's insert method.
///
/// # Examples
/// ```rust
/// use cycle_map::optionals::OptionalPair;
///
/// let op: OptionalPair<String, String> = OptionalPair::SomeLeft("Hello".to_string());
///
/// match op {
///     OptionalPair::None => { /*...*/ },
///     OptionalPair::SomeLeft(left) => { /*...*/ },
///     OptionalPair::SomeRight(right) => { /*...*/ },
///     OptionalPair::SomeBoth(left, right) => { /*...*/ },
/// }
/// ```
#[derive(PartialEq, Eq)]
pub enum OptionalPair<L, R>
where
    L: Eq,
    R: Eq,
{
    /// Equivalent to `Option`'s `None` variant
    None,
    /// Equivalent to `Some(Some((left, right)), None)`
    SomeLeft(L),
    /// Equivalent to `Some(None, Some((left, right)))`
    SomeRight(R),
    /// Equivalent to `Some(Some((l1, r1)), Some(l2, r2))`
    SomeBoth(L, R),
}

/// A shorthand for an optional pair of tuples used in some map insert methods
pub type InsertOptional<L, R> = OptionalPair<(L, R), (L, R)>;
//pub type SwapOptional<I, P> = OptionalPair<I, P>;

impl<L, R> OptionalPair<L, R>
where
    L: Eq,
    R: Eq,
{
    /// Returns true if `self` is `OptionalPair::None` and false otherwise
    pub fn is_none(&self) -> bool {
        *self == OptionalPair::None
    }

    /// Returns the negation of [`is_none`]
    ///
    /// [`is_none`]: enum.OptionalPair.html#method.is_none
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    /// Return an optional reference to the left item
    pub fn get_left(&self) -> Option<&L> {
        match self {
            Self::SomeLeft(l) | Self::SomeBoth(l, _) => Some(l),
            _ => None,
        }
    }

    /// Return an optional reference to the right item
    pub fn get_right(&self) -> Option<&R> {
        match self {
            Self::SomeRight(r) | Self::SomeBoth(_, r) => Some(r),
            _ => None,
        }
    }

    /// Converts the pair into a new pair. The types of the new pair need to implement a
    /// converation `From` the old types. This consumes the old pair
    pub fn convert<A, B>(self) -> OptionalPair<A, B>
    where
        A: Eq + From<L>,
        B: Eq + From<R>,
    {
        self.map(|l| A::from(l), |r| B::from(r))
    }

    /// Maps both inner values of a pair, consuming this pair.
    pub fn map<A, B, LF, RF>(self, left: LF, right: RF) -> OptionalPair<A, B>
    where
        A: Eq,
        B: Eq,
        LF: FnOnce(L) -> A,
        RF: FnOnce(R) -> B,
    {
        match self {
            Self::None => OptionalPair::None,
            Self::SomeLeft(l) => OptionalPair::SomeLeft(left(l)),
            Self::SomeRight(r) => OptionalPair::SomeRight(right(r)),
            Self::SomeBoth(l, r) => OptionalPair::SomeBoth(left(l), right(r)),
        }
    }

    /// Maps left inner value of a pair, consuming this pair.
    pub fn map_left<A, F>(self, f: F) -> OptionalPair<A, R>
    where
        A: Eq,
        F: FnOnce(L) -> A,
    {
        match self {
            Self::None => OptionalPair::None,
            Self::SomeRight(r) => OptionalPair::SomeRight(r),
            Self::SomeLeft(l) => OptionalPair::SomeLeft(f(l)),
            Self::SomeBoth(l, r) => OptionalPair::SomeBoth(f(l), r),
        }
    }

    /// Maps right inner value of a pair, consuming this pair.
    pub fn map_right<A, F>(self, f: F) -> OptionalPair<L, A>
    where
        A: Eq,
        F: FnOnce(R) -> A,
    {
        match self {
            Self::None => OptionalPair::None,
            Self::SomeLeft(l) => OptionalPair::SomeLeft(l),
            Self::SomeRight(r) => OptionalPair::SomeRight(f(r)),
            Self::SomeBoth(l, r) => OptionalPair::SomeBoth(l, f(r)),
        }
    }
}

impl<L, R> OptionalPair<&L, &R>
where
    L: Eq + Clone,
    R: Eq + Clone,
{
    /// Takes an `OptionalPair` that contains references to clonable values and returns an
    /// `OptionalPair` of clones of those values.
    pub fn cloned(&self) -> OptionalPair<L, R> {
        match self {
            Self::None => OptionalPair::None,
            Self::SomeLeft(l) => OptionalPair::SomeLeft((*l).clone()),
            Self::SomeRight(r) => OptionalPair::SomeRight((*r).clone()),
            Self::SomeBoth(l, r) => OptionalPair::SomeBoth((*l).clone(), (*r).clone()),
        }
    }
}

impl<L, R> Clone for OptionalPair<L, R>
where
    L: Eq + Clone,
    R: Eq + Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::None => OptionalPair::None,
            Self::SomeLeft(l) => OptionalPair::SomeLeft(l.clone()),
            Self::SomeRight(r) => OptionalPair::SomeRight(r.clone()),
            Self::SomeBoth(l, r) => OptionalPair::SomeBoth(l.clone(), r.clone()),
        }
    }
}

impl<L, R> fmt::Debug for OptionalPair<L, R>
where
    L: fmt::Debug + Eq,
    R: fmt::Debug + Eq,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => {
                write!(f, "None")
            }
            Self::SomeLeft(item) => {
                write!(f, "SomeLeft( {item:?} )")
            }
            Self::SomeRight(item) => {
                write!(f, "SomeRight( {item:?} )")
            }
            Self::SomeBoth(l_item, r_item) => {
                write!(f, "SomeBoth( {l_item:?}, {r_item:?} )")
            }
        }
    }
}

impl<L, R> From<(Option<L>, Option<R>)> for OptionalPair<L, R>
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: (Option<L>, Option<R>)) -> Self {
        match input_pair {
            (None, None) => Self::None,
            (Some(item), None) => Self::SomeLeft(item),
            (None, Some(item)) => Self::SomeRight(item),
            (Some(item_1), Some(item_2)) => Self::SomeBoth(item_1, item_2),
        }
    }
}

impl<L, R> From<Option<(Option<L>, Option<R>)>> for OptionalPair<L, R>
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: Option<(Option<L>, Option<R>)>) -> Self {
        match input_pair {
            None | Some((None, None)) => Self::None,
            Some((Some(item), None)) => Self::SomeLeft(item),
            Some((None, Some(item))) => Self::SomeRight(item),
            Some((Some(item_1), Some(item_2))) => Self::SomeBoth(item_1, item_2),
        }
    }
}

impl<L, R> From<OptionalPair<L, R>> for (Option<L>, Option<R>)
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: OptionalPair<L, R>) -> Self {
        match input_pair {
            OptionalPair::None => (None, None),
            OptionalPair::SomeLeft(item) => (Some(item), None),
            OptionalPair::SomeRight(item) => (None, Some(item)),
            OptionalPair::SomeBoth(item_1, item_2) => (Some(item_1), Some(item_2)),
        }
    }
}

impl<L, R> From<OptionalPair<L, R>> for Option<(Option<L>, Option<R>)>
where
    L: Eq,
    R: Eq,
{
    fn from(input_pair: OptionalPair<L, R>) -> Self {
        match input_pair {
            OptionalPair::None => None,
            OptionalPair::SomeLeft(item) => Some((Some(item), None)),
            OptionalPair::SomeRight(item) => Some((None, Some(item))),
            OptionalPair::SomeBoth(item_1, item_2) => Some((Some(item_1), Some(item_2))),
        }
    }
}
