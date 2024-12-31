#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

/// A little-endian equivilant to `From`.
pub trait FromLE<T>: Sized {
    /// Converts the value into an instance of Self, where the value should be treated as
    /// little-endian.
    fn from_le(value: T) -> Self;
}

/// A little-endian equivilant to `TryFrom`.
pub trait TryFromLE<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to convert a value into an instance of Self, where the value should be treated as
    /// little-endian.
    fn try_from_le(value: T) -> Result<Self, Self::Error>;
}

/// A little-endian equivilant to `Into`.
pub trait IntoLE<T>: Sized {
    /// Converts self into a value, where the value should be treated as little-endian.
    fn into_le(self) -> T;
}

/// A little-endian equivilant to `TryInto`.
pub trait TryIntoLE<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to convert self into a value, where that value should be treated as little-endian.
    fn try_into_le(self) -> Result<T, Self::Error>;
}

impl<T, U> TryFromLE<U> for T
where
    T: FromLE<U>
{
    type Error = ();

    fn try_from_le(value: U) -> Result<Self, Self::Error> {
        Ok(T::from_le(value))
    }
}

impl<T, U> IntoLE<U> for T
where
    U: FromLE<T>
{
    fn into_le(self) -> U {
        U::from_le(self)
    }
}

impl<T, U> TryIntoLE<U> for T
where
    U: TryFromLE<T>
{
    type Error = U::Error;

    fn try_into_le(self) -> Result<U, Self::Error> {
        U::try_from_le(self)
    }
}

/// A big-endian equivilant to `From`.
pub trait FromBE<T>: Sized {
    /// Converts the value into an instance of Self, where the value should be treated as
    /// big-endian.
    fn from_be(value: T) -> Self;
}

/// A big-endian equivilant to `TryFrom`.
pub trait TryFromBE<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to convert a value into an instance of Self, where the value should be treated as
    /// big-endian.
    fn try_from_be(value: T) -> Result<Self, Self::Error>;
}

/// A big-endian equivilant to `Into`.
pub trait IntoBE<T>: Sized {
    /// Converts self into a value, where that value should be treated as big-endian.
    fn into_be(self) -> T;
}

/// A big-endian equivilant to `TryInto`.
pub trait TryIntoBE<T>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to convert self into a value, where that value should be treated as big-endian.
    fn try_into_be(self) -> Result<T, Self::Error>;
}

impl<T, U> TryFromBE<U> for T
where
    T: FromBE<U>
{
    type Error = ();

    fn try_from_be(value: U) -> Result<Self, Self::Error> {
        Ok(T::from_be(value))
    }
}

impl<T, U> IntoBE<U> for T
where
    U: FromBE<T>
{
    fn into_be(self) -> U {
        U::from_be(self)
    }
}

impl<T, U> TryIntoBE<U> for T
where
    U: TryFromBE<T>
{
    type Error = U::Error;

    fn try_into_be(self) -> Result<U, Self::Error> {
        U::try_from_be(self)
    }
}
