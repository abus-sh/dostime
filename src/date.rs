#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

#[cfg(feature = "serde-1")]
use serde_derive::{Deserialize, Serialize};

use crate::traits::{FromBE, FromLE, IntoLE, TryFromBE, TryFromLE, TryIntoBE};

/// A date in MS-DOS format.
/// 
/// MS-DOS dates are typically stored as little-endian 2-byte values. The 5 lowest order bits are
/// the day, the 4 middle bits are the month, and the 7 highest bits are the year offest from 1980.
/// 
/// ```
/// use dostime::DOSDate;
/// 
/// let date1 = DOSDate::new(2017, 4, 6).unwrap();
/// let date2 = DOSDate::try_from(0x4A86).unwrap();
/// let date3 = DOSDate::try_from([0x86, 0x4A]).unwrap();
/// 
/// assert_eq!(date1, date2);
/// assert_eq!(date1, date3);
/// 
/// let int: u16 = date1.into();
/// assert_eq!(int, 0x4A86);
/// 
/// let bytes: [u8; 2] = date2.into();
/// assert_eq!(bytes, [0x86, 0x4A]);
/// ```
/// 
/// For example, `0x4A86` (big-endian) is `0b0100101010000110`, which corresponds to 2017-04-06. See
/// below for a working out of the conversion.
/// 
/// `0x4A86` -> `0b0100101010000110` -> `0100101 0100 00110` -> `37 4 6` -> `2017-04-06`
/// 
/// The functions that convert to and from `u16`s interpret the value as big-endian since that makes
/// the math easier. The functions that convert to and from `[u8; 2]` interpret the value as
/// little-endian since bytes are usually stored as little-endian values.
/// 
/// Not all 2-byte sequences correspond to a valid date. For example, the array `[0xB1, 0x2B]`
/// would become the date 2001-13-17, which is clearly invalid. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSDate`s can be converted into a valid 2-byte sequence (hence the use
/// of `Into`).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct DOSDate {
    year: u16,
    month: u8,
    day: u8,
}

/// A list of possible errors that could happen when constructing a date.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DateError {
    /// The year is before 1980 or after 2107.
    InvalidYear,
    /// The month is less than 1 (January) or greater than 12 (December).
    InvalidMonth,
    /// The day is 0, greater than 31, or could not exist in the current month.
    InvalidDay,
}

impl DOSDate {
    /// Attempts to create a new instance of a `DOSDate`. If the year, month, or day is invalid,
    /// then the creation fails and an error is returned.
    /// 
    /// A year is invalid if it is before 1980 or after 2107. DOS dates can't represent any time
    /// before or after that year. A month is invalid if it is 0 or greater than 12 since the months
    /// are represented by 1 (January) to 12 (December). A day is invalid if it is 0, greater than
    /// 31, or it could not exist in the given month/year (ex. 4/31/XXXX is invalid, 2/29/2003 is
    /// invalid).
    /// 
    /// ```
    /// use dostime::DOSDate;
    /// use dostime::date::DateError;
    /// 
    /// // Construct valid dates.
    /// let date1 = DOSDate::new(1980, 1, 1).unwrap();
    /// let date2 = DOSDate::new(2000, 3, 4).unwrap();
    /// 
    /// // Invalid dates can't be constructed.
    /// let bad_year = DOSDate::new(1979, 12, 1).unwrap_err();
    /// assert_eq!(bad_year, DateError::InvalidYear);
    /// 
    /// let bad_month = DOSDate::new(2000, 13, 1).unwrap_err();
    /// assert_eq!(bad_month, DateError::InvalidMonth);
    /// 
    /// let bad_day = DOSDate::new(2000, 11, 31).unwrap_err();
    /// assert_eq!(bad_day, DateError::InvalidDay);
    /// ```
    pub fn new(year: u16, month: u8, day: u8) -> Result<Self, DateError> {
        let date = Self {
            year,
            month,
            day,
        };

        if let Err(err) = date.validate() {
            return Err(err);
        }

        Ok(date)
    }

    /// Creates a new instance of a `DOSDate`. If the year, month, or day is invalid, then the
    /// function panics.
    /// 
    /// A year is invalid if it is before 1980 or after 2107. DOS dates can't represent any time
    /// before or after that year. A month is invalid if it is 0 or greater than 12 since the months
    /// are represented by 1 (January) to 12 (December). A day is invalid if it is 0, greater than
    /// 31, or it could not exist in the given month/year (ex. 4/31/XXXX is invalid, 2/29/2003 is
    /// invalid).
    /// 
    /// ```
    /// use dostime::DOSDate;
    /// 
    /// // Construct valid dates normally.
    /// let date1 = DOSDate::new_or_panic(1980, 1, 1);
    /// let date2 = DOSDate::new_or_panic(2000, 3, 4);
    /// ```
    /// 
    /// ```should_panic
    /// use dostime::DOSDate;
    /// 
    /// // Invalid dates panic
    /// DOSDate::new_or_panic(2000, 11, 31);
    /// ```
    pub fn new_or_panic(year: u16, month: u8, day: u8) -> Self {
        let date = Self {
            year,
            month,
            day,
        };

        if let Err(_) = date.validate() {
            panic!("Invalid dates may not be constructed.");
        }

        date
    }

    /// Returns the year for this `DOSDate`.
    pub fn year(&self) -> u16 {
        self.year
    }

    /// Returns the month for this `DOSDate`.
    pub fn month(&self) -> u8 {
        self.month
    }

    /// Returns the day for this `DOSDate`.
    pub fn day(&self) -> u8 {
        self.day
    }

    /// Determines if the date is actually a real date that could be represented by a DOS date. If
    /// the date is invalid, then a `DateError` is returned.
    fn validate(&self) -> Result<(), DateError> {
        // Dates before 1980 can't be represented as an unsigned int, must be invalid
        // Dates after 2107 can't be represented in the amount of space available, must be invalid
        if self.year < 1980 || self.year > 2107 {
            return Err(DateError::InvalidYear);
        }

        // Day 0 is invalid
        if self.day == 0 {
            return Err(DateError::InvalidDay);
        }

        // Handle each month seperately
        match self.month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => {
                if self.day > 31 {
                    return Err(DateError::InvalidDay);
                }
            },
            4 | 6 | 9 | 11 => {
                if self.day > 30 {
                    return Err(DateError::InvalidDay);
                }
            },
            2 => {
                // Handle leap years
                // Every 4 years
                // If year is divisible by 100, skip it
                // If year is divisible by 400, have it anyways
                let mut leap_year = false;
                if self.year % 4 == 0 {
                    leap_year = true;
                    if self.year % 100 == 0 {
                        leap_year = false;
                        if self.year % 400 == 0 {
                            leap_year = true;
                        }
                    }
                }
                if leap_year && self.day > 29 {
                    return Err(DateError::InvalidDay);
                }
                if !leap_year && self.day > 28 {
                    return Err(DateError::InvalidDay);
                }
            },
            _ => return Err(DateError::InvalidMonth)
        }

        Ok(())
    }
}

impl TryFromBE<u16> for DOSDate {
    type Error = DateError;

    fn try_from_be(value: u16) -> Result<Self, Self::Error> {
        let year = ((value & 0b1111111000000000) >> 9) + 1980;
        let month = ((value & 0b0000000111100000) >> 5) as u8;
        let day = (value & 0b0000000000011111) as u8;

        let date = Self {
            year,
            month,
            day,
        };

        if let Err(err) = date.validate() {
            return Err(err)
        }

        Ok(date)
    }
}

impl TryFrom<u16> for DOSDate {
    type Error = DateError;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        value.try_into_be()
    }
}

impl From<DOSDate> for u16 {
    fn from(value: DOSDate) -> Self {
        // Shift year to be last 5 bits of u16
        let year = (value.year - 1980) << 9;

        // Shift month to be middle 4 bits of u16
        let month = (value.month as u16) << 5;
        
        // Sum year, month, and day to create result
        year + month + (value.day as u16)
    }
}

impl TryFromLE<[u8; 2]> for DOSDate {
    type Error = DateError;

    fn try_from_le(value: [u8; 2]) -> Result<Self, Self::Error> {
        DOSDate::try_from(u16::from_le_bytes(value))
    }
}

impl TryFromBE<[u8; 2]> for DOSDate {
    type Error = DateError;

    fn try_from_be(value: [u8; 2]) -> Result<Self, Self::Error> {
        DOSDate::try_from(u16::from_be_bytes(value))
    }
}

impl TryFrom<[u8; 2]> for DOSDate {
    type Error = DateError;

    fn try_from(value: [u8; 2]) -> Result<Self, Self::Error> {
        DOSDate::try_from_le(value)
    }
}

impl FromLE<DOSDate> for [u8; 2] {
    fn from_le(value: DOSDate) -> Self {
        let bytes: u16 = value.into();
        bytes.to_le_bytes()
    }
}

impl FromBE<DOSDate> for [u8; 2] {
    fn from_be(value: DOSDate) -> Self {
        let bytes: u16 = value.into();
        bytes.to_be_bytes()
    }
}

impl From<DOSDate> for [u8; 2] {
    fn from(value: DOSDate) -> Self {
        value.into_le()
    }
}

impl Default for DOSDate {
    fn default() -> Self {
        Self {
            year: 1980,
            month: 1,
            day: 1,
        }
    }
}

impl Display for DOSDate {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:0>4}-{:0>2}-{:0>2}", self.year, self.month, self.day)
    }
}

#[cfg(feature = "time-1")]
mod time {
    use time::{Date, Month};

    use super::{DOSDate, DateError};

    impl From<DOSDate> for Date {
        fn from(value: DOSDate) -> Self {
            let month: Month = value.month.try_into()
                .expect("DOSDate was constructed with an invalid month.");

            Self::from_calendar_date(value.year as i32, month, value.day)
                .expect("DOSDate contained an invalid date.")
        }
    }

    impl TryFrom<Date> for DOSDate {
        type Error = DateError;

        fn try_from(value: Date) -> Result<Self, Self::Error> {
            let year: u16 = match value.year().try_into() {
                Err(_) => return Err(DateError::InvalidYear),
                Ok(year) => year,
            };

            Self::new(year, value.month() as u8, value.day())
        }
    }

    #[cfg(test)]
    mod tests {
        use time::{Date, Month};

        use crate::DOSDate;

        #[test]
        fn test_from_time_date() {
            // Test valid dates
            // 1980-01-01 - epoch
            let ddate = DOSDate::new(1980, 1, 1).unwrap();
            let tdate = Date::from_calendar_date(1980, Month::January, 1).unwrap();
            let tdate: DOSDate = tdate.try_into().unwrap();
            assert_eq!(ddate, tdate);

            // 2017-04-06
            let ddate = DOSDate::new(2017, 4, 6).unwrap();
            let tdate = Date::from_calendar_date(2017, Month::April, 6).unwrap();
            let tdate: DOSDate = tdate.try_into().unwrap();
            assert_eq!(ddate, tdate);

            // 2107-12-31 - last possible date
            let ddate = DOSDate::new(2107, 12, 31).unwrap();
            let tdate = Date::from_calendar_date(2107, Month::December, 31).unwrap();
            let tdate: DOSDate = tdate.try_into().unwrap();
            assert_eq!(ddate, tdate);

            // 2016-02-29 - leap year
            let ddate = DOSDate::new(2016, 2, 29).unwrap();
            let tdate = Date::from_calendar_date(2016, Month::February, 29).unwrap();
            let tdate: DOSDate = tdate.try_into().unwrap();
            assert_eq!(ddate, tdate);

            // 2000-02-29 - leap year, divisible by 400
            let ddate = DOSDate::new(2000, 2, 29).unwrap();
            let tdate = Date::from_calendar_date(2000, Month::February, 29).unwrap();
            let tdate: DOSDate = tdate.try_into().unwrap();
            assert_eq!(ddate, tdate);

            // Test invalid dates
            // 1979-12-31 - too early
            let tdate = Date::from_calendar_date(1979, Month::December, 31).unwrap();
            assert!(DOSDate::try_from(tdate).is_err());

            // 2108-01-01 - too late
            let tdate = Date::from_calendar_date(2108, Month::January, 1).unwrap();
            assert!(DOSDate::try_from(tdate).is_err());
        }

        #[test]
        fn test_to_time_date() {
            // 1980-01-01 - epoch
            let ddate = DOSDate::new(1980, 1, 1).unwrap();
            let ddate: Date = ddate.into();
            let tdate = Date::from_calendar_date(1980, Month::January, 1).unwrap();
            assert_eq!(ddate, tdate);

            // 2017-04-06
            let ddate = DOSDate::new(2017, 4, 6).unwrap();
            let ddate: Date = ddate.into();
            let tdate = Date::from_calendar_date(2017, Month::April, 6).unwrap();
            assert_eq!(ddate, tdate);

            // 2107-12-31 - last possible date
            let ddate = DOSDate::new(2107, 12, 31).unwrap();
            let ddate: Date = ddate.into();
            let tdate = Date::from_calendar_date(2107, Month::December, 31).unwrap();
            assert_eq!(ddate, tdate);

            // 2016-02-29 - leap year
            let ddate = DOSDate::new(2016, 2, 29).unwrap();
            let ddate: Date = ddate.into();
            let tdate = Date::from_calendar_date(2016, Month::February, 29).unwrap();
            assert_eq!(ddate, tdate);

            // 2000-02-29 - leap year, divisible by 400
            let ddate = DOSDate::new(2000, 2, 29).unwrap();
            let ddate: Date = ddate.into();
            let tdate = Date::from_calendar_date(2000, Month::February, 29).unwrap();
            assert_eq!(ddate, tdate);
        }
    }
}

#[cfg(feature = "chrono-1")]
mod chrono {
    use chrono::{Datelike, NaiveDate};

    use super::{DOSDate, DateError};

    impl From<DOSDate> for NaiveDate {
        fn from(value: DOSDate) -> Self {
            NaiveDate::from_ymd_opt(value.year as i32, value.month as u32, value.day as u32)
                .expect("DOSDate contained an invalid date.")
        }
    }

    impl TryFrom<NaiveDate> for DOSDate {
        type Error = DateError;

        fn try_from(value: NaiveDate) -> Result<Self, Self::Error> {
            let year: u16 = match value.year().try_into() {
                Err(_) => return Err(DateError::InvalidYear),
                Ok(year) => year,
            };

            Self::new(year, value.month() as u8, value.day() as u8)
        }
    }

    #[cfg(test)]
    mod tests {
        use chrono::NaiveDate;

        use crate::DOSDate;

        #[test]
        fn test_from_chrono_date() {
            // Test valid dates
            // 1980-01-01 - epoch
            let ddate = DOSDate::new(1980, 1, 1).unwrap();
            let cdate = NaiveDate::from_ymd_opt(1980, 1, 1).unwrap();
            let cdate: DOSDate = cdate.try_into().unwrap();
            assert_eq!(ddate, cdate);

            // 2017-04-06
            let ddate = DOSDate::new(2017, 4, 6).unwrap();
            let cdate = NaiveDate::from_ymd_opt(2017, 4, 6).unwrap();
            let cdate: DOSDate = cdate.try_into().unwrap();
            assert_eq!(ddate, cdate);

            // 2107-12-31 - last possible date
            let ddate = DOSDate::new(2107, 12, 31).unwrap();
            let cdate = NaiveDate::from_ymd_opt(2107, 12, 31).unwrap();
            let cdate: DOSDate = cdate.try_into().unwrap();
            assert_eq!(ddate, cdate);

            // 2016-02-29 - leap year
            let ddate = DOSDate::new(2016, 2, 29).unwrap();
            let cdate = NaiveDate::from_ymd_opt(2016, 2, 29).unwrap();
            let cdate: DOSDate = cdate.try_into().unwrap();
            assert_eq!(ddate, cdate);

            // 2000-02-29 - leap year, divisible by 400
            let ddate = DOSDate::new(2000, 2, 29).unwrap();
            let cdate = NaiveDate::from_ymd_opt(2000, 2, 29).unwrap();
            let cdate: DOSDate = cdate.try_into().unwrap();
            assert_eq!(ddate, cdate);

            // Test invalid dates
            // 1979-12-31 - too early
            let cdate = NaiveDate::from_ymd_opt(1979, 12, 31).unwrap();
            assert!(DOSDate::try_from(cdate).is_err());

            // 2108-01-01 - too late
            let cdate = NaiveDate::from_ymd_opt(2108, 1, 1).unwrap();
            assert!(DOSDate::try_from(cdate).is_err());
        }

        #[test]
        fn test_to_chrono_date() {
            // 1980-01-01 - epoch
            let ddate = DOSDate::new(1980, 1, 1).unwrap();
            let ddate: NaiveDate = ddate.into();
            let cdate = NaiveDate::from_ymd_opt(1980, 1, 1).unwrap();
            assert_eq!(ddate, cdate);

            // 2017-04-06
            let ddate = DOSDate::new(2017, 4, 6).unwrap();
            let ddate: NaiveDate = ddate.into();
            let cdate = NaiveDate::from_ymd_opt(2017, 4, 6).unwrap();
            assert_eq!(ddate, cdate);

            // 2107-12-31 - last possible date
            let ddate = DOSDate::new(2107, 12, 31).unwrap();
            let ddate: NaiveDate = ddate.into();
            let cdate = NaiveDate::from_ymd_opt(2107, 12, 31).unwrap();
            assert_eq!(ddate, cdate);

            // 2016-02-29 - leap year
            let ddate = DOSDate::new(2016, 2, 29).unwrap();
            let ddate: NaiveDate = ddate.into();
            let cdate = NaiveDate::from_ymd_opt(2016, 2, 29).unwrap();
            assert_eq!(ddate, cdate);

            // 2000-02-29 - leap year, divisible by 400
            let ddate = DOSDate::new(2000, 2, 29).unwrap();
            let ddate: NaiveDate = ddate.into();
            let cdate = NaiveDate::from_ymd_opt(2000, 2, 29).unwrap();
            assert_eq!(ddate, cdate);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::IntoBE;

    use super::*;

    #[test]
    fn test_new() {
        // Test detecting if a date is valid

        // Test valid dates
        // 1980-01-01 - epoch
        let date = DOSDate::new(1980, 1, 1).unwrap();
        assert_eq!(date, DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        let date = DOSDate::new(2017, 4, 6).unwrap();
        assert_eq!(date, DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        let date = DOSDate::new(2107, 12, 31).unwrap();
        assert_eq!(date, DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        let date = DOSDate::new(2016, 2, 29).unwrap();
        assert_eq!(date, DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        let date = DOSDate::new(2000, 2, 29).unwrap();
        assert_eq!(date, DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // Test invalid dates
        // 1979-12-31 - low year
        let error = DOSDate::new(1979, 12, 31).unwrap_err();
        assert_eq!(error, DateError::InvalidYear);

        // 2108-01-01 - high year
        let error = DOSDate::new(2108, 1, 1).unwrap_err();
        assert_eq!(error, DateError::InvalidYear);

        // 1999-00-02 - low month
        let error = DOSDate::new(1999, 0, 2).unwrap_err();
        assert_eq!(error, DateError::InvalidMonth);

        // 2001-13-17 - high month
        let error = DOSDate::new(2001, 13, 17).unwrap_err();
        assert_eq!(error, DateError::InvalidMonth);

        // 2020-05-00 - low day
        let error = DOSDate::new(2020, 5, 0).unwrap_err();
        assert_eq!(error, DateError::InvalidDay);

        // 2003-02-29 - non-leap year
        let error = DOSDate::new(2003, 2, 29).unwrap_err();
        assert_eq!(error, DateError::InvalidDay);

        // 2100-02-29 - non-leap year, divisible by 100
        let error = DOSDate::new(2100, 2, 29).unwrap_err();
        assert_eq!(error, DateError::InvalidDay);
    }

    #[test]
    fn test_new_or_panic() {
        // Test valid dates
        // 1980-01-01 - epoch
        let date = DOSDate::new_or_panic(1980, 1, 1);
        assert_eq!(date, DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        let date = DOSDate::new_or_panic(2017, 4, 6);
        assert_eq!(date, DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        let date = DOSDate::new_or_panic(2107, 12, 31);
        assert_eq!(date, DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        let date = DOSDate::new_or_panic(2016, 2, 29);
        assert_eq!(date, DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        let date = DOSDate::new_or_panic(2000, 2, 29);
        assert_eq!(date, DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });
    }

    #[test]
    #[should_panic]
    fn test_new_or_panic_inv_year() {
        DOSDate::new_or_panic(1979, 12, 31);
    }

    #[test]
    #[should_panic]
    fn test_new_or_panic_inv_month() {
        DOSDate::new_or_panic(2000, 13, 31);
    }

    #[test]
    #[should_panic]
    fn test_new_or_panic_inv_day() {
        DOSDate::new_or_panic(2000, 11, 31);
    }

    #[test]
    fn test_date_from_u16() {
        // Test converting from a u16 to a DOSDate

        // Test valid dates
        // 1980-01-01 - epoch
        assert_eq!(DOSDate::try_from(0x0021).unwrap(), DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        assert_eq!(DOSDate::try_from(0x4A86).unwrap(), DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        assert_eq!(DOSDate::try_from(0xFF9F).unwrap(), DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        assert_eq!(DOSDate::try_from(0x485D).unwrap(), DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        assert_eq!(DOSDate::try_from(0x285D).unwrap(), DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // Test invalid dates
        // 1999-00-02 - low month
        assert_eq!(
            DOSDate::try_from(0x2602).expect_err("Low month allowed."),
            DateError::InvalidMonth
        );

        // 2001-13-17 - high month
        assert_eq!(
            DOSDate::try_from(0x2BB1).expect_err("High month allowed."),
            DateError::InvalidMonth
        );

        // 2020-05-00 - low day
        assert_eq!(
            DOSDate::try_from(0x28A0).expect_err("Low day allowed."),
            DateError::InvalidDay
        );

        // 2003-02-29 - non-leap year
        assert_eq!(
            DOSDate::try_from(0x2E5D).expect_err("2/29 allowed on non-leap year."),
            DateError::InvalidDay
        );

        // 2100-02-29 - non-leap year, divisible by 100
        assert_eq!(
            DOSDate::try_from(0xF05D).expect_err("2/29 allowed on non-leap year divisible by 100."),
            DateError::InvalidDay
        );
    }

    #[test]
    fn test_date_to_u16() {
        // Test converting to a u16 from a DOSDate

        // 1980-01-01 - epoch
        let date: u16 = DOSDate {
            year: 1980,
            month: 1,
            day: 1
        }.into();
        assert_eq!(date, 0x0021);

        // 2017-04-06
        let date: u16 = DOSDate {
            year: 2017,
            month: 4,
            day: 6
        }.into();
        assert_eq!(date, 0x4A86);

        // 2107-12-31 - last possible date
        let date: u16 = DOSDate {
            year: 2107,
            month: 12,
            day: 31
        }.into();
        assert_eq!(date, 0xFF9F);

        // 2016-02-29 - leap year
        let date: u16 = DOSDate {
            year: 2016,
            month: 2,
            day: 29
        }.into();
        assert_eq!(date, 0x485D);

        // 2000-02-29 - leap year, divisible by 400
        let date: u16 = DOSDate {
            year: 2000,
            month: 2,
            day: 29
        }.into();
        assert_eq!(date, 0x285D);
    }

    #[test]
    fn test_date_from_u8arr_le() {
        // Test converting from a [u8; 2] to a DOSDate

        // Test valid dates
        // 1980-01-01 - epoch
        assert_eq!(DOSDate::try_from_le([0x21, 0x00]).unwrap(), DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        assert_eq!(DOSDate::try_from_le([0x86, 0x4A]).unwrap(), DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        assert_eq!(DOSDate::try_from_le([0x9F, 0xFF]).unwrap(), DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        assert_eq!(DOSDate::try_from_le([0x5D, 0x28]).unwrap(), DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        assert_eq!(DOSDate::try_from_le([0x5D, 0x28]).unwrap(), DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // Test invalid dates
        // 1999-00-02 - low month
        assert_eq!(
            DOSDate::try_from_le([0x02, 0x26]).expect_err("Low month allowed."),
            DateError::InvalidMonth
        );

        // 2001-13-17 - high month
        assert_eq!(
            DOSDate::try_from_le([0xB1, 0x2B]).expect_err("High month allowed."),
            DateError::InvalidMonth
        );

        // 2020-05-00 - low day
        assert_eq!(
            DOSDate::try_from_le([0xA0, 0x28]).expect_err("Low day allowed."),
            DateError::InvalidDay
        );

        // 2003-02-29 - non-leap year
        assert_eq!(
            DOSDate::try_from_le([0x5D, 0x2E]).expect_err("2/29 allowed on non-leap year."),
            DateError::InvalidDay
        );

        // 2100-02-29 - non-leap year, divisible by 100
        assert_eq!(
            DOSDate::try_from_le([0x5D, 0xF0]).expect_err("2/29 allowed on non-leap year divisible by 100."),
            DateError::InvalidDay
        );
    }

    #[test]
    fn test_date_from_u8arr_be() {
        // Test converting from a [u8; 2] to a DOSDate

        // Test valid dates
        // 1980-01-01 - epoch
        assert_eq!(DOSDate::try_from_be([0x00, 0x21]).unwrap(), DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        assert_eq!(DOSDate::try_from_be([0x4A, 0x86]).unwrap(), DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        assert_eq!(DOSDate::try_from_be([0xFF, 0x9F]).unwrap(), DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        assert_eq!(DOSDate::try_from_be([0x48, 0x5D]).unwrap(), DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        assert_eq!(DOSDate::try_from_be([0x28, 0x5D]).unwrap(), DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // Test invalid dates
        // 1999-00-02 - low month
        assert_eq!(
            DOSDate::try_from_be([0x26, 0x02]).expect_err("Low month allowed."),
            DateError::InvalidMonth
        );

        // 2001-13-17 - high month
        assert_eq!(
            DOSDate::try_from_be([0x2B, 0xB1]).expect_err("High month allowed."),
            DateError::InvalidMonth
        );

        // 2020-05-00 - low day
        assert_eq!(
            DOSDate::try_from_be([0x28, 0xA0]).expect_err("Low day allowed."),
            DateError::InvalidDay
        );

        // 2003-02-29 - non-leap year
        assert_eq!(
            DOSDate::try_from_be([0x2E, 0x5D]).expect_err("2/29 allowed on non-leap year."),
            DateError::InvalidDay
        );

        // 2100-02-29 - non-leap year, divisible by 100
        assert_eq!(
            DOSDate::try_from_be([0xF0, 0x5D]).expect_err("2/29 allowed on non-leap year divisible by 100."),
            DateError::InvalidDay
        );
    }

    #[test]
    fn test_date_from_u8arr() {
        // Test converting from a [u8; 2] to a DOSDate

        // Test valid dates
        // 1980-01-01 - epoch
        assert_eq!(DOSDate::try_from([0x21, 0x00]).unwrap(), DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        });

        // 2017-04-06
        assert_eq!(DOSDate::try_from([0x86, 0x4A]).unwrap(), DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        });

        // 2107-12-31 - last possible date
        assert_eq!(DOSDate::try_from([0x9F, 0xFF]).unwrap(), DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        });

        // 2016-02-29 - leap year
        assert_eq!(DOSDate::try_from([0x5D, 0x48]).unwrap(), DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        });

        // 2000-02-29 - leap year, divisible by 400
        assert_eq!(DOSDate::try_from([0x5D, 0x28]).unwrap(), DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        });

        // Test invalid dates
        // 1999-00-02 - low month
        assert_eq!(
            DOSDate::try_from([0x02, 0x26]).expect_err("Low month allowed."),
            DateError::InvalidMonth
        );

        // 2001-13-17 - high month
        assert_eq!(
            DOSDate::try_from([0xB1, 0x2B]).expect_err("High month allowed."),
            DateError::InvalidMonth
        );

        // 2020-05-00 - low day
        assert_eq!(
            DOSDate::try_from([0xA0, 0x28]).expect_err("Low day allowed."),
            DateError::InvalidDay
        );

        // 2003-02-29 - non-leap year
        assert_eq!(
            DOSDate::try_from([0x5D, 0x2E]).expect_err("2/29 allowed on non-leap year."),
            DateError::InvalidDay
        );

        // 2100-02-29 - non-leap year, divisible by 100
        assert_eq!(
            DOSDate::try_from([0x5D, 0xF0]).expect_err("2/29 allowed on non-leap year divisible by 100."),
            DateError::InvalidDay
        );
    }

    #[test]
    fn test_date_to_u8arr_le() {
        // Test converting to a [u8; 2] from a DOSDate

        // 1980-01-01 - epoch
        let date: [u8; 2] = DOSDate {
            year: 1980,
            month: 1,
            day: 1
        }.into_le();
        assert_eq!(date, [0x21, 0x00]);

        // 2017-04-06
        let date: [u8; 2] = DOSDate {
            year: 2017,
            month: 4,
            day: 6
        }.into_le();
        assert_eq!(date, [0x86, 0x4A]);

        // 2107-12-31 - last possible date
        let date: [u8; 2] = DOSDate {
            year: 2107,
            month: 12,
            day: 31
        }.into_le();
        assert_eq!(date, [0x9F, 0xFF]);

        // 2016-02-29 - leap year
        let date: [u8; 2] = DOSDate {
            year: 2016,
            month: 2,
            day: 29
        }.into_le();
        assert_eq!(date, [0x5D, 0x48]);

        // 2000-02-29 - leap year, divisible by 400
        let date: [u8; 2] = DOSDate {
            year: 2000,
            month: 2,
            day: 29
        }.into_le();
        assert_eq!(date, [0x5D, 0x28]);
    }

    #[test]
    fn test_date_to_u8arr_be() {
        // Test converting to a [u8; 2] from a DOSDate

        // 1980-01-01 - epoch
        let date: [u8; 2] = DOSDate {
            year: 1980,
            month: 1,
            day: 1
        }.into_be();
        assert_eq!(date, [0x00, 0x21]);

        // 2017-04-06
        let date: [u8; 2] = DOSDate {
            year: 2017,
            month: 4,
            day: 6
        }.into_be();
        assert_eq!(date, [0x4A, 0x86]);

        // 2107-12-31 - last possible date
        let date: [u8; 2] = DOSDate {
            year: 2107,
            month: 12,
            day: 31
        }.into_be();
        assert_eq!(date, [0xFF, 0x9F]);

        // 2016-02-29 - leap year
        let date: [u8; 2] = DOSDate {
            year: 2016,
            month: 2,
            day: 29
        }.into_be();
        assert_eq!(date, [0x48, 0x5D]);

        // 2000-02-29 - leap year, divisible by 400
        let date: [u8; 2] = DOSDate {
            year: 2000,
            month: 2,
            day: 29
        }.into_be();
        assert_eq!(date, [0x28, 0x5D]);
    }

    #[test]
    fn test_date_to_u8arr() {
        // Test converting to a [u8; 2] from a DOSDate

        // 1980-01-01 - epoch
        let date: [u8; 2] = DOSDate {
            year: 1980,
            month: 1,
            day: 1
        }.into();
        assert_eq!(date, [0x21, 0x00]);

        // 2017-04-06
        let date: [u8; 2] = DOSDate {
            year: 2017,
            month: 4,
            day: 6
        }.into();
        assert_eq!(date, [0x86, 0x4A]);

        // 2107-12-31 - last possible date
        let date: [u8; 2] = DOSDate {
            year: 2107,
            month: 12,
            day: 31
        }.into();
        assert_eq!(date, [0x9F, 0xFF]);

        // 2016-02-29 - leap year
        let date: [u8; 2] = DOSDate {
            year: 2016,
            month: 2,
            day: 29
        }.into();
        assert_eq!(date, [0x5D, 0x48]);

        // 2000-02-29 - leap year, divisible by 400
        let date: [u8; 2] = DOSDate {
            year: 2000,
            month: 2,
            day: 29
        }.into();
        assert_eq!(date, [0x5D, 0x28]);
    }
}
