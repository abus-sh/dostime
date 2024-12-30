#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

use crate::{dosdate::{DOSDate, DateError}, dostime::{DOSTime, TimeError}};

/// A datetime in MS-Dos format.
/// 
/// Datetimes are often stored as little-endian 4 byte values, with the first 2 bytes representing
/// the time and the second 2 bytes representing the date. For a more complete explanation on time
/// format, see the documentation for `DOSDate` and `DOSTime`.
/// 
/// The functions that convert to and from `u32`s interpret the value as big-endian since that is
/// consistent with the behavior of the `u16` conversion for `DOSDate` and `DOSTime`. The functions
/// that convert to and from `[u8; 4]` interpret the values as little-endian since the bytes are
/// often stored as little-endian values.
/// 
/// Not all 4 byte sequences correspond to a valid datetime. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSDateTime`s can be converted into a valid 4 byte sequence (hence the
/// use of `Into`).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
    /// Construct a new datetime from an existing date and time.
    /// 
    /// ```
    /// use ::dostime::dosdatetime;
    /// use ::dostime::dostime;
    /// use ::dostime::dosdate;
    /// 
    /// let date1 = dosdate::DOSDate::new(2017, 4, 6).unwrap();
    /// let date2 = dosdate::DOSDate::new(2000, 1, 2).unwrap();
    /// 
    /// let time1 = dostime::DOSTime::new(0, 3, 12).unwrap();
    /// let time2 = dostime::DOSTime::new(15, 21, 19).unwrap();
    /// 
    /// let datetime1 = dosdatetime::DOSDateTime::new(date1, time1);
    /// let datetime2 = dosdatetime::DOSDateTime::new(date2, time2);
    /// ```
    pub fn new(date: DOSDate, time: DOSTime) -> Self {
        Self {
            date,
            time,
        }
    }
}

impl TryFrom<u32> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
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

impl Into<u32> for DOSDateTime {
    fn into(self) -> u32 {
        let date: u16 = self.date.into();
        let date = (date as u32) << 16;

        let time: u16 = self.time.into();
        let time = time as u32;

        date + time
    }
}

impl TryFrom<[u8; 4]> for DOSDateTime {
    type Error = DateTimeError;

    fn try_from(value: [u8; 4]) -> Result<Self, Self::Error> {
        DOSDateTime::try_from(u32::from_le_bytes(value))
    }
}

impl Into<[u8; 4]> for DOSDateTime {
    fn into(self) -> [u8; 4] {
        let bytes: u32 = self.into();
        bytes.to_le_bytes()
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

#[cfg(feature = "std")]
impl Display for DOSDateTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.date, self.time)
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
