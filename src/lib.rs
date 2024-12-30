#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![cfg_attr(not(feature = "std"), no_std)]

//! This crate converts `DOSTime`s, `DOSDate`s, `DOSDateTime`s to and from binary and integer
//! formats. This crate is no_std compatible.
//! 
//! An explanation of the date and time formats can be found
//! [here](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-dosdatetimetofiletime),
//! though the documentation for `DOSTime` and `DOSDate` also includes explantions for the format.
//! 
//! By default, this crate treats integers as big-endian and arrays as little-endian. In the future,
//! support for treating arrays as big-endian will be added.

// TODO: create try_from_le and try_from_be for DOSTime & DOSDate that uses [u8; 2]

/// In cases where big-endian vs little-endian differences matter, this module contains traits that
/// can be used to define `Into`, `TryInto`, `From`, and `TryFrom` equivalents that are specifically
/// little- or big-endian.
//pub mod traits;

/// This module contains `DOSTime` and its related functionality. It allows for conversion to and
/// from `DOSTime` and related types.
pub mod dostime;

/// This module contains `DOSDate` and its related functionality. It allows for conversion to and
/// from `DOSDate` and related types.
pub mod dosdate;

/// This module contains `DOSDateTime` and its related functionality. It allows for conversion to
/// and from `DOSDateTime` and related types.
pub mod dosdatetime;
