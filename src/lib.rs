#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]
#![cfg_attr(not(feature = "std"), no_std)]

//! This crate converts MS DOS times to and from various formats, including integers, byte arrays, and
//! types in external crates (see the features for more information).
//! 
//! An explanation of the date and time formats can be found
//! [here](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-dosdatetimetofiletime),
//! though the documentation for `DOSTime` and `DOSDate` also includes explantions for the format.
//! 
//! ```
//! use dostime::{DOSDate, DOSTime, DOSDateTime};
//! use dostime::date::DateError;
//! use dostime::time::TimeError;
//! use dostime::datetime::DateTimeError;
//! 
//! // Valid dates and times can be constructed.
//! let date = DOSDate::new(2017, 4, 6).unwrap();           // 2017-04-06
//! let time = DOSTime::new(13, 24, 54).unwrap();           // 13:24:54
//! let datetime = DOSDateTime::new(2006, 4, 15, 1, 5, 34); // 2006-04-15 01:05:34
//! 
//! // Invalid dates and times can't be constructed and information about what is invalid is
//! // returned.
//! let invalid_month = DOSDate::new(1996, 13, 3).unwrap_err();
//! assert_eq!(invalid_month, DateError::InvalidMonth);
//! 
//! let invalid_second = DOSTime::new(1, 2, 60).unwrap_err();
//! assert_eq!(invalid_second, TimeError::InvalidSecond);
//! 
//! let invalid_day = DOSDateTime::new(2001, 4, 31, 6, 13, 12).unwrap_err();
//! assert_eq!(invalid_day, DateTimeError::DateError(DateError::InvalidDay));
//! 
//! // Dates and times can be converted to and from integers and arrays of bytes.
//! let int: u16 = date.into();
//! assert_eq!(int, 0x4A86);
//! assert_eq!(date, DOSDate::try_from(0x4A86).unwrap());
//! 
//! let bytes: [u8; 2] = time.into();
//! assert_eq!(bytes, [0x1B, 0x6B]);
//! assert_eq!(time, DOSTime::try_from([0x1B, 0x6B]).unwrap());
//! ```
//! 
//! # Features
//! 
//! - `std` (default) - enables features that rely on the standard library
//! - `serde-1` - enables (de)serialization with Serde
//! - `time-1` - enables conversion to/from types in the `time` crate (`Date`, `Time`, and
//! `PrimitiveDateTime`)
//! - `chrono-1` - enables conversion to/from types in the `chrono` crate (`NaiveDate`, `NaiveTime`, and
//! `NaiveDateTime`)

/// In cases where big-endian vs little-endian differences matter, this module contains traits that
/// can be used to define `Into`, `TryInto`, `From`, and `TryFrom` equivalents that are specifically
/// little- or big-endian.
/// 
/// As with the normal traits, `FromLE` creates implementations of `TryFromLE` and `IntoLE` and
/// `IntoLE` creates an implementation of `TryIntoLE`. This also applies for the big-endian trait
/// variants.
pub mod traits;

/// This module contains `DOSTime` and its related functionality. It allows for conversion to and
/// from `DOSTime` and related types.
pub mod time;
pub use time::DOSTime;

/// This module contains `DOSDate` and its related functionality. It allows for conversion to and
/// from `DOSDate` and related types.
pub mod date;
pub use date::DOSDate;

/// This module contains `DOSDateTime` and its related functionality. It allows for conversion to
/// and from `DOSDateTime` and related types.
pub mod datetime;
pub use datetime::DOSDateTime;
