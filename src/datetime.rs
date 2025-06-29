#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

#[cfg(feature = "serde-1")]
use serde_derive::{Deserialize, Serialize};

use crate::{date::{DOSDate, DateError}, time::{DOSTime, TimeError}, traits::{FromBE, FromLE, IntoLE, TryFromBE, TryFromLE, TryIntoBE}};

/// A datetime in MS-Dos format.
/// 
/// Datetimes are often stored as little-endian 4-byte values, with the first 2-bytes representing
/// the time and the second 2-bytes representing the date. For a more complete explanation on time
/// format, see the documentation for `DOSDate` and `DOSTime`.
/// 
/// ```
/// use dostime::{DOSDate, DOSTime, DOSDateTime};
/// 
/// let date = DOSDate::new(2017, 4, 6).unwrap();
/// let time = DOSTime::new(13, 24, 54).unwrap();
/// 
/// let datetime1 = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
/// let datetime2 = DOSDateTime::try_from((date, time)).unwrap();
/// let datetime3 = DOSDateTime::try_from([0x1B, 0x6B, 0x86, 0x4A]).unwrap();
/// 
/// assert_eq!(datetime1, datetime2);
/// assert_eq!(datetime1, datetime3);
/// 
/// let int: u32 = datetime1.into();
/// assert_eq!(int, 0x4A86_6B1B);
/// 
/// let bytes: [u8; 4] = datetime2.into();
/// assert_eq!(bytes, [0x1B, 0x6B, 0x86, 0x4A]);
/// ```
/// 
/// The functions that convert to and from `u32`s interpret the value as big-endian since that is
/// consistent with the behavior of the `u16` conversion for `DOSDate` and `DOSTime`. The functions
/// that convert to and from `[u8; 4]` interpret the values as little-endian since the bytes are
/// often stored as little-endian values.
/// 
/// Not all 4-byte sequences correspond to a valid datetime. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSDateTime`s can be converted into a valid 4-byte sequence (hence the
/// use of `Into`).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct DOSDateTime {
    date: DOSDate,
    time: DOSTime,
}

/// A list of possible errors that could happen when constructing a datetime. Relies on the errors
/// described by `dosdate::DateError` and `dostime::TimeError`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DateTimeError {
    /// The date was invalid. The exact error is enclosed.
    DateError(DateError),
    /// The time was invalid. The exact error is enclosed.
    TimeError(TimeError),
}

impl DOSDateTime {
    /// Attempts to construct a new instance of `DOSDateTime`. If any aspect of the datetime is
    /// invalid, then the creation fails and an error is returned. The error returned is based on
    /// the error returned by `DOSDate::new` or `DOSTime::new`.
    /// 
    /// ```
    /// use dostime::DOSDateTime;
    /// use dostime::datetime::DateTimeError;
    /// use dostime::date::DateError;
    /// use dostime::time::TimeError;
    /// 
    /// // Construct valid datetimes.
    /// let datetime1 = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
    /// let datetime2 = DOSDateTime::new(1980, 1, 1, 0, 0, 0).unwrap();
    /// 
    /// // Invalid datetimes can't be constructed.
    /// let bad_date = DOSDateTime::new(2011, 2, 29, 14, 0, 2).unwrap_err();
    /// assert_eq!(bad_date, DateTimeError::DateError(DateError::InvalidDay));
    /// 
    /// let bad_time = DOSDateTime::new(1994, 9, 15, 14, 50, 60).unwrap_err();
    /// assert_eq!(bad_time, DateTimeError::TimeError(TimeError::InvalidSecond));
    /// ```
    pub fn new(year: u16, month: u8, day: u8, hour: u8, minute: u8, second: u8) -> Result<Self, DateTimeError> {
        let date = match DOSDate::new(year, month, day) {
            Err(err) => return Err(DateTimeError::DateError(err)),
            Ok(date) => date,
        };

        let time = match DOSTime::new(hour, minute, second) {
            Err(err) => return Err(DateTimeError::TimeError(err)),
            Ok(time) => time,
        };

        Ok(Self {
            date,
            time,
        })
    }

    /// Creates a new instance of a `DOSDateTime`. If any aspect of the datetime is invalid, then
    /// the function panics.
    /// 
    /// ```
    /// use dostime::DOSDateTime;
    /// 
    /// // Construct valid dates normally.
    /// let date1 = DOSDateTime::new_or_panic(1980, 1, 1, 0, 0, 0);
    /// let date2 = DOSDateTime::new_or_panic(2000, 3, 4, 15, 21, 19);
    /// ```
    /// 
    /// ```should_panic
    /// use dostime::DOSDateTime;
    /// 
    /// // Invalid dates panic
    /// DOSDateTime::new_or_panic(2000, 11, 31, 12, 13, 14);
    /// ```
    pub fn new_or_panic(year: u16, month: u8, day: u8, hour: u8, minute: u8, second: u8) -> Self {
        let date = match DOSDate::new(year, month, day) {
            Err(_) => panic!("Invalid dates may not be constructed."),
            Ok(date) => date,
        };

        let time = match DOSTime::new(hour, minute, second) {
            Err(_) => panic!("Invalid times may not be constructed."),
            Ok(time) => time,
        };

        Self {
            date,
            time,
        }
    }

    /// Returns the year for this `DOSDate`.
    pub fn year(&self) -> u16 {
        self.date.year()
    }

    /// Returns the month for this `DOSDate`.
    pub fn month(&self) -> u8 {
        self.date.month()
    }

    /// Returns the day for this `DOSDate`.
    pub fn day(&self) -> u8 {
        self.date.day()
    }

    /// Returns the hour for this `DOSTime`.
    pub fn hour(&self) -> u8 {
        self.time.hour()
    }

    /// Returns the minute for this `DOSTime`.
    pub fn minute(&self) -> u8 {
        self.time.minute()
    }

    /// Returns the second for this `DOSTime`.
    pub fn second(&self) -> u8 {
        self.time.second()
    }
}

impl From<(DOSDate, DOSTime)> for DOSDateTime {
    fn from(value: (DOSDate, DOSTime)) -> Self {
        let (date, time) = value;
        
        Self {
            date,
            time,
        }
    }
}

impl TryFromBE<u32> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from_be(value: u32) -> Result<Self, Self::Error> {
        let date = (value >> 16) as u16;
        let time = (value & 0xFFFF) as u16;

        let date = match DOSDate::try_from(date) {
            Err(err) => return Err(DateTimeError::DateError(err)),
            Ok(date) => date,
        };

        let time = match DOSTime::try_from(time) {
            Err(err) => return Err(DateTimeError::TimeError(err)),
            Ok(time) => time,
        };

        Ok(Self {
            date,
            time,
        })
    }
}

impl TryFrom<u32> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        value.try_into_be()
    }
}

impl From<DOSDateTime> for u32 {
    fn from(value: DOSDateTime) -> Self {
        let date: u16 = value.date.into();
        let date = (date as u32) << 16;

        let time: u16 = value.time.into();
        let time = time as u32;

        date + time
    }
}

impl TryFromLE<[u8; 4]> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from_le(value: [u8; 4]) -> Result<Self, Self::Error> {
        DOSDateTime::try_from(u32::from_le_bytes(value))
    }
}

impl TryFromBE<[u8; 4]> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from_be(value: [u8; 4]) -> Result<Self, Self::Error> {
        DOSDateTime::try_from(u32::from_be_bytes(value))
    }
}

impl TryFrom<[u8; 4]> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from(value: [u8; 4]) -> Result<Self, Self::Error> {
        DOSDateTime::try_from_le(value)
    }
}

impl FromLE<DOSDateTime> for [u8; 4] {
    fn from_le(value: DOSDateTime) -> Self {
        let bytes: u32 = value.into();
        bytes.to_le_bytes()
    }
} 

impl FromBE<DOSDateTime> for [u8; 4] {
    fn from_be(value: DOSDateTime) -> Self {
        let bytes: u32 = value.into();
        bytes.to_be_bytes()
    }
}

impl From<DOSDateTime> for [u8; 4] {
    fn from(value: DOSDateTime) -> Self {
        value.into_le()
    }
}

impl Default for DOSDateTime {
    fn default() -> Self {
        Self {
            date: DOSDate::default(),
            time: DOSTime::default(),
        }
    }
}

impl Display for DOSDateTime {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{} {}", self.date, self.time)
    }
}

#[cfg(feature = "time-1")]
mod time {
    use time::{Date, PrimitiveDateTime, Time};

    use crate::{DOSDate, DOSTime};

    use super::{DOSDateTime, DateTimeError};

    impl From<DOSDateTime> for PrimitiveDateTime {
        fn from(value: DOSDateTime) -> Self {
            let date: Date = value.date.into();
            let time: Time = value.time.into();

            Self::new(date, time)
        }
    }

    impl TryFrom<PrimitiveDateTime> for DOSDateTime {
        type Error = DateTimeError;

        fn try_from(value: PrimitiveDateTime) -> Result<Self, Self::Error> {
            let date: DOSDate = match value.date().try_into() {
                Err(err) => return Err(DateTimeError::DateError(err)),
                Ok(date) => date,
            };

            let time: DOSTime = value.time().into();

            Ok(DOSDateTime::from((date, time)))
        }
    }

    #[cfg(test)]
    mod tests {
        use time::{Date, Month, PrimitiveDateTime, Time};

        use crate::DOSDateTime;

        #[test]
        fn test_from_time_datetime() {
            // Test valid datetimes
            // 1980-01-01 00:00:00 - epoch
            let ddatetime = DOSDateTime::new(1980, 1, 1, 0, 0, 0).unwrap();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(1980, Month::January, 1).unwrap(),
                Time::from_hms(0, 0, 0).unwrap(),
            );
            let tdatetime: DOSDateTime = tdatetime.try_into().unwrap();
            assert_eq!(ddatetime, tdatetime);

            // 2017-04-06 13:24:54
            let ddatetime = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(2017, Month::April, 6).unwrap(),
                Time::from_hms(13, 24, 54).unwrap(),
            );
            let tdatetime: DOSDateTime = tdatetime.try_into().unwrap();
            assert_eq!(ddatetime, tdatetime);

            // 2107-12-31 23:59:58 - last possible datetime
            let ddatetime = DOSDateTime::new(2107, 12, 31, 23, 59, 58).unwrap();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(2107, Month::December, 31).unwrap(),
                Time::from_hms(23, 59, 58).unwrap(),
            );
            let tdatetime: DOSDateTime = tdatetime.try_into().unwrap();
            assert_eq!(ddatetime, tdatetime);

            // Test invalid datetimes
            // 1979-12-31 23:59:59 - too early
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(1979, Month::December, 31).unwrap(),
                Time::from_hms(23, 59, 59).unwrap(),
            );
            assert!(DOSDateTime::try_from(tdatetime).is_err());

            // 2108-01-01 00:00:00- too late
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(2108, Month::January, 1).unwrap(),
                Time::from_hms(0, 0, 0).unwrap(),
            );
            assert!(DOSDateTime::try_from(tdatetime).is_err());
        }

        #[test]
        fn test_to_time_datetime() {
            // 1980-01-01 00:00:00 - epoch
            let ddatetime = DOSDateTime::new(1980, 1, 1, 0, 0, 0).unwrap();
            let ddatetime: PrimitiveDateTime = ddatetime.into();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(1980, Month::January, 1).unwrap(),
                Time::from_hms(0, 0, 0).unwrap(),
            );
            assert_eq!(ddatetime, tdatetime);

            // 2017-04-06 13:24:54
            let ddatetime = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
            let ddatetime: PrimitiveDateTime = ddatetime.into();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(2017, Month::April, 6).unwrap(),
                Time::from_hms(13, 24, 54).unwrap(),
            );
            assert_eq!(ddatetime, tdatetime);

            // 2107-12-31 23:59:58 - last possible datetime
            let ddatetime = DOSDateTime::new(2107, 12, 31, 23, 59, 58).unwrap();
            let ddatetime: PrimitiveDateTime = ddatetime.into();
            let tdatetime = PrimitiveDateTime::new(
                Date::from_calendar_date(2107, Month::December, 31).unwrap(),
                Time::from_hms(23, 59, 58).unwrap(),
            );
            assert_eq!(ddatetime, tdatetime);
        }
    }
}

#[cfg(feature = "chrono-1")]
mod chrono {
    use chrono::{NaiveDate, NaiveDateTime, NaiveTime};

    use crate::{DOSDate, DOSTime};

    use super::{DOSDateTime, DateTimeError};

    impl From<DOSDateTime> for NaiveDateTime {
        fn from(value: DOSDateTime) -> Self {
            let date: NaiveDate = value.date.into();
            let time: NaiveTime = value.time.into();

            Self::new(date, time)
        }
    }

    impl TryFrom<NaiveDateTime> for DOSDateTime {
        type Error = DateTimeError;

        fn try_from(value: NaiveDateTime) -> Result<Self, Self::Error> {
            let date: DOSDate = match value.date().try_into() {
                Err(err) => return Err(DateTimeError::DateError(err)),
                Ok(date) => date,
            };

            let time: DOSTime = value.time().into();

            Ok(DOSDateTime::from((date, time)))
        }
    }

    #[cfg(test)]
    mod tests {
        use chrono::{NaiveDate, NaiveDateTime, NaiveTime};

        use crate::DOSDateTime;

        #[test]
        fn test_from_chrono_datetime() {
            // Test valid datetimes
            // 1980-01-01 00:00:00 - epoch
            let ddatetime = DOSDateTime::new(1980, 1, 1, 0, 0, 0).unwrap();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(1980, 1, 1).unwrap(),
                NaiveTime::from_hms_opt(0, 0, 0).unwrap(),
            );
            let cdatetime: DOSDateTime = cdatetime.try_into().unwrap();
            assert_eq!(ddatetime, cdatetime);

            // 2017-04-06 13:24:54
            let ddatetime = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(2017, 4, 6).unwrap(),
                NaiveTime::from_hms_opt(13, 24, 54).unwrap(),
            );
            let cdatetime: DOSDateTime = cdatetime.try_into().unwrap();
            assert_eq!(ddatetime, cdatetime);

            // 2107-12-31 23:59:58 - last possible datetime
            let ddatetime = DOSDateTime::new(2107, 12, 31, 23, 59, 58).unwrap();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(2107, 12, 31).unwrap(),
                NaiveTime::from_hms_opt(23, 59, 58).unwrap(),
            );
            let cdatetime: DOSDateTime = cdatetime.try_into().unwrap();
            assert_eq!(ddatetime, cdatetime);

            // Test invalid datetimes
            // 1979-12-31 23:59:59 - too early
            let tdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(1979, 12, 31).unwrap(),
                NaiveTime::from_hms_opt(23, 59, 59).unwrap(),
            );
            assert!(DOSDateTime::try_from(tdatetime).is_err());

            // 2108-01-01 00:00:00- too late
            let tdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(2108, 1, 1).unwrap(),
                NaiveTime::from_hms_opt(0, 0, 0).unwrap(),
            );
            assert!(DOSDateTime::try_from(tdatetime).is_err());
        }

        #[test]
        fn test_to_chrono_datetime() {
            // Test valid datetimes
            // 1980-01-01 00:00:00 - epoch
            let ddatetime = DOSDateTime::new(1980, 1, 1, 0, 0, 0).unwrap();
            let ddatetime: NaiveDateTime = ddatetime.into();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(1980, 1, 1).unwrap(),
                NaiveTime::from_hms_opt(0, 0, 0).unwrap(),
            );
            assert_eq!(ddatetime, cdatetime);

            // 2017-04-06 13:24:54
            let ddatetime = DOSDateTime::new(2017, 4, 6, 13, 24, 54).unwrap();
            let ddatetime: NaiveDateTime = ddatetime.into();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(2017, 4, 6).unwrap(),
                NaiveTime::from_hms_opt(13, 24, 54).unwrap(),
            );
            assert_eq!(ddatetime, cdatetime);

            // 2107-12-31 23:59:58 - last possible datetime
            let ddatetime = DOSDateTime::new(2107, 12, 31, 23, 59, 58).unwrap();
            let ddatetime: NaiveDateTime = ddatetime.into();
            let cdatetime = NaiveDateTime::new(
                NaiveDate::from_ymd_opt(2107, 12, 31).unwrap(),
                NaiveTime::from_hms_opt(23, 59, 58).unwrap(),
            );
            assert_eq!(ddatetime, cdatetime);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_datetime_from_u32() {
        // Test converting from a u32 to a DOSDateTime

        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        assert_eq!(DOSDateTime::try_from(0x0021_0000).unwrap(), DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        });

        // 2017-04-06 13:24:54
        assert_eq!(DOSDateTime::try_from(0x4A86_6B1B).unwrap(), DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        });

        // 2107-12-31 23:59:58 - last possible datetime
        assert_eq!(DOSDateTime::try_from(0xFF9F_BF7D).unwrap(), DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        });
        
        // Test invalid dates
        // 1999-00-02 00:00:00 - low month
        //assert!(DOSDateTime::try_from(0x2602_0000).is_err());
        assert_eq!(
            DOSDateTime::try_from(0x2602_0000).expect_err("Low month allowed"),
            DateTimeError::DateError(DateError::InvalidMonth),
        );

        // 2001-13-17 00:00:00 - high month
        assert!(DOSDateTime::try_from(0x2BB1_0000).is_err());

        // 2020-05-00 00:00:00 - low day
        assert!(DOSDateTime::try_from(0x28A0_0000).is_err());

        // 2003-02-29 00:00:00 - non-leap year
        assert!(DOSDateTime::try_from(0x2E5D_0000).is_err());

        // 2100-02-29 00:00:00 - non-leap year, divisible by 100
        assert!(DOSDateTime::try_from(0xF05D_0000).is_err());

        // Test invalid times
        // 1980-01-01 24:00:00 - high hour
        assert!(DOSDateTime::try_from(0x0021_C000).is_err());

        // 1980-01-01 00:60:00 - high minute
        assert!(DOSDateTime::try_from(0x0021_0780).is_err());

        // 1980-01-01 00:00:60 - high second
        assert!(DOSDateTime::try_from(0x0021_001E).is_err());
    }

    #[test]
    fn test_datetime_to_u32() {
        // Test converting to a u32 from a DOSDateTime
        
        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        let datetime: u32 = DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        }.into();
        assert_eq!(datetime, 0x0021_0000);

        // 2017-04-06 13:24:54
        let datetime: u32 = DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        }.into();
        assert_eq!(datetime, 0x4A86_6B1B);

        // 2107-12-31 23:59:58 - last possible datetime
        let datetime: u32 = DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        }.into();
        assert_eq!(datetime, 0xFF9F_BF7D);
    }

    #[test]
    fn test_datetime_from_u8arr_le() {
        // Test converting from a [u8; 4] to a DOSDateTime
        
        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        assert_eq!(DOSDateTime::try_from_le([0x00, 0x00, 0x21, 0x00]).unwrap(), DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        });

        // 2017-04-06 13:24:54
        assert_eq!(DOSDateTime::try_from_le([0x1B, 0x6B, 0x86, 0x4A]).unwrap(), DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        });

        // 2107-12-31 23:59:58 - last possible datetime
        assert_eq!(DOSDateTime::try_from_le([0x7D, 0xBF, 0x9F, 0xFF]).unwrap(), DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        });
        
        // Test invalid dates
        // 1999-00-02 00:00:00 - low month
        assert!(DOSDateTime::try_from_le([0x00, 0x00, 0x02, 0x26]).is_err());

        // 2001-13-17 00:00:00 - high month
        assert!(DOSDateTime::try_from_le([0x00, 0x00, 0xB1, 0x2B]).is_err());

        // 2020-05-00 00:00:00 - low day
        assert!(DOSDateTime::try_from_le([0x00, 0x00, 0xA0, 0x28]).is_err());

        // 2003-02-29 00:00:00 - non-leap year
        assert!(DOSDateTime::try_from_le([0x00, 0x00, 0x5D, 0x2E]).is_err());

        // 2100-02-29 00:00:00 - non-leap year, divisible by 100
        assert!(DOSDateTime::try_from_le([0x00, 0x00, 0x5D, 0xF0]).is_err());

        // Test invalid times
        // 1980-01-01 24:00:00 - high hour
        assert!(DOSDateTime::try_from_le([0x00, 0xC0, 0x21, 0x00]).is_err());

        // 1980-01-01 00:60:00 - high minute
        assert!(DOSDateTime::try_from_le([0x80, 0x07, 0x21, 0x00]).is_err());

        // 1980-01-01 00:00:60 - high second
        assert!(DOSDateTime::try_from_le([0x1E, 0x00, 0x21, 0x00]).is_err());
    }

    #[test]
    fn test_datetime_from_u8arr_be() {
        // Test converting from a [u8; 4] to a DOSDateTime
        
        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        assert_eq!(DOSDateTime::try_from_be([0x00, 0x21, 0x00, 0x00]).unwrap(), DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        });

        // 2017-04-06 13:24:54
        assert_eq!(DOSDateTime::try_from_be([0x4A, 0x86, 0x6B, 0x1B]).unwrap(), DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        });

        // 2107-12-31 23:59:58 - last possible datetime
        assert_eq!(DOSDateTime::try_from_be([0xFF, 0x9F, 0xBF, 0x7D]).unwrap(), DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        });
        
        // Test invalid dates
        // 1999-00-02 00:00:00 - low month
        assert!(DOSDateTime::try_from_be([0x26, 0x02, 0x00, 0x00]).is_err());

        // 2001-13-17 00:00:00 - high month
        assert!(DOSDateTime::try_from_be([0x2B, 0xB1, 0x00, 0x00]).is_err());

        // 2020-05-00 00:00:00 - low day
        assert!(DOSDateTime::try_from_be([0x28, 0xA0, 0x00, 0x00]).is_err());

        // 2003-02-29 00:00:00 - non-leap year
        assert!(DOSDateTime::try_from_be([0x2E, 0x5D, 0x00, 0x00]).is_err());

        // 2100-02-29 00:00:00 - non-leap year, divisible by 100
        assert!(DOSDateTime::try_from_be([0xF0, 0x5D, 0x00, 0x00]).is_err());

        // Test invalid times
        // 1980-01-01 24:00:00 - high hour
        assert!(DOSDateTime::try_from_be([0x00, 0x21, 0xC0, 0x00]).is_err());

        // 1980-01-01 00:60:00 - high minute
        assert!(DOSDateTime::try_from_be([0x00, 0x21, 0x07, 0x80]).is_err());

        // 1980-01-01 00:00:60 - high second
        assert!(DOSDateTime::try_from_be([0x00, 0x21, 0x00, 0x1E]).is_err());
    }

    #[test]
    fn test_datetime_from_u8arr() {
        // Test converting from a [u8; 4] to a DOSDateTime
        
        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        assert_eq!(DOSDateTime::try_from([0x00, 0x00, 0x21, 0x00]).unwrap(), DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        });

        // 2017-04-06 13:24:54
        assert_eq!(DOSDateTime::try_from([0x1B, 0x6B, 0x86, 0x4A]).unwrap(), DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        });

        // 2107-12-31 23:59:58 - last possible datetime
        assert_eq!(DOSDateTime::try_from([0x7D, 0xBF, 0x9F, 0xFF]).unwrap(), DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        });
        
        // Test invalid dates
        // 1999-00-02 00:00:00 - low month
        assert!(DOSDateTime::try_from([0x00, 0x00, 0x02, 0x26]).is_err());

        // 2001-13-17 00:00:00 - high month
        assert!(DOSDateTime::try_from([0x00, 0x00, 0xB1, 0x2B]).is_err());

        // 2020-05-00 00:00:00 - low day
        assert!(DOSDateTime::try_from([0x00, 0x00, 0xA0, 0x28]).is_err());

        // 2003-02-29 00:00:00 - non-leap year
        assert!(DOSDateTime::try_from([0x00, 0x00, 0x5D, 0x2E]).is_err());

        // 2100-02-29 00:00:00 - non-leap year, divisible by 100
        assert!(DOSDateTime::try_from([0x00, 0x00, 0x5D, 0xF0]).is_err());

        // Test invalid times
        // 1980-01-01 24:00:00 - high hour
        assert!(DOSDateTime::try_from([0x00, 0xC0, 0x21, 0x00]).is_err());

        // 1980-01-01 00:60:00 - high minute
        assert!(DOSDateTime::try_from([0x80, 0x07, 0x21, 0x00]).is_err());

        // 1980-01-01 00:00:60 - high second
        assert!(DOSDateTime::try_from([0x1E, 0x00, 0x21, 0x00]).is_err());
    }

    #[test]
    fn test_datetime_to_u8arr() {
        // Test converting to a [u8; 4] from a DOSDateTime

        // Test valid datetimes
        // 1980-01-01 00:00:00 - epoch
        let datetime: [u8; 4] = DOSDateTime {
            date: DOSDate::new(1980, 1, 1).unwrap(),
            time: DOSTime::new(0, 0, 0).unwrap(),
        }.into();
        assert_eq!(datetime, [0x00, 0x00, 0x21, 0x00]);

        // 2017-04-06 13:24:54
        let datetime: [u8; 4] = DOSDateTime {
            date: DOSDate::new(2017, 4, 6).unwrap(),
            time: DOSTime::new(13, 24, 54).unwrap(),
        }.into();
        assert_eq!(datetime, [0x1B, 0x6B, 0x86, 0x4A]);

        // 2107-12-31 23:59:58 - last possible datetime
        let datetime: [u8; 4] = DOSDateTime {
            date: DOSDate::new(2107, 12, 31).unwrap(),
            time: DOSTime::new(23, 59, 58).unwrap(),
        }.into();
        assert_eq!(datetime, [0x7D, 0xBF, 0x9F, 0xFF]);
    }
}
