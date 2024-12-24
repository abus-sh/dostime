#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

/// A date in MS-DOS format.
/// 
/// MS-DOS dates are typically stored as little-endian 2 byte values. The 5 lowest order bits are
/// the day, the 4 middle bits are the month, and the 7 highest bits are the year offest from 1980.
/// 
/// ```
/// let date = DOSDate::try_from(0x4A86).unwrap();
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
/// Not all 2 byte sequences correspond to a valid date. For example, the array `[0xB1, 0x2B]`
/// would become the date 2001-13-17, which is clearly invalid. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSDate`s can be converted into a valid 2 byte sequence (hence the use
/// of `Into`).
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DOSDate {
    year: u16,
    month: u8,
    day: u8,
}

impl DOSDate {
    fn is_valid(&self) -> bool {
        // Dates before 1980 can't be represented as an unsigned int, must be invalid
        if self.year < 1980 {
            return false;
        }

        // Day 0 is invalid
        if self.day == 0 {
            return false;
        }

        // Handle each month seperately
        match self.month {
            1 | 3 | 5 | 7 | 8 | 10 | 12 => {
                if self.day > 31 {
                    return false;
                }
            },
            4 | 6 | 9 | 11 => {
                if self.day > 30 {
                    return false;
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
                    return false;
                }
                if !leap_year && self.day > 28 {
                    return false;
                }
            },
            _ => return false
        }

        true
    }
}

impl TryFrom<u16> for DOSDate {
    type Error = ();

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        let year = ((value & 0b1111111000000000) >> 9) + 1980;
        let month = ((value & 0b0000000111100000) >> 5) as u8;
        let day = (value & 0b0000000000011111) as u8;

        let date = Self {
            year,
            month,
            day,
        };

        if !date.is_valid() {
            return Err(());
        }

        Ok(date)
    }
}

impl Into<u16> for DOSDate {
    fn into(self) -> u16 {
        // Shift year to be last 5 bits of u16
        let year = (self.year - 1980) << 9;

        // Shift month to be middle 4 bits of u16
        let month = (self.month as u16) << 5;
        
        // Sum year, month, and day to create result
        year + month + (self.day as u16)
    }
}

impl TryFrom<[u8; 2]> for DOSDate {
    type Error = ();

    fn try_from(value: [u8; 2]) -> Result<Self, Self::Error> {
        DOSDate::try_from(u16::from_le_bytes(value))
    }
}

impl Into<[u8; 2]> for DOSDate {
    fn into(self) -> [u8; 2] {
        let bytes: u16 = self.into();
        bytes.to_le_bytes()
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

#[cfg(feature = "std")]
impl Display for DOSDate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:0>4}-{:0>2}-{:0>2}", self.year, self.month, self.day)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl DOSDate {
        pub fn debug_new(year: u16, month: u8, day: u8) -> Self {
            Self {
                year,
                month,
                day,
            }
        }
    }

    #[test]
    fn test_is_valid() {
        // Test detecting if a date is valid

        // Test valid dates
        // 1980-01-01 - epoch
        assert!(DOSDate {
            year: 1980,
            month: 1,
            day: 1,
        }.is_valid());

        // 2017-04-06
        assert!(DOSDate {
            year: 2017,
            month: 4,
            day: 6,
        }.is_valid());

        // 2107-12-31 - last possible date
        assert!(DOSDate {
            year: 2107,
            month: 12,
            day: 31,
        }.is_valid());

        // 2016-02-29 - leap year
        assert!(DOSDate {
            year: 2016,
            month: 2,
            day: 29,
        }.is_valid());

        // 2000-02-29 - leap year, divisible by 400
        assert!(DOSDate {
            year: 2000,
            month: 2,
            day: 29,
        }.is_valid());

        // Test invalid dates
        // 1999-00-02 - low month
        assert!(!DOSDate {
            year: 1999,
            month: 0,
            day: 2,
        }.is_valid());

        // 2001-13-17 - high month
        assert!(!DOSDate {
            year: 2001,
            month: 13,
            day: 17,
        }.is_valid());

        // 2020-05-00 - low day
        assert!(!DOSDate {
            year: 2020,
            month: 5,
            day: 0,
        }.is_valid());

        // 2003-02-29 - non-leap year
        assert!(!DOSDate {
            year: 2003,
            month: 2,
            day: 29,
        }.is_valid());

        // 2100-02-29 - non-leap year, divisible by 100
        assert!(!DOSDate {
            year: 2100,
            month: 2,
            day: 29,
        }.is_valid());
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
        assert!(DOSDate::try_from(0x2602).is_err());

        // 2001-13-17 - high month
        assert!(DOSDate::try_from(0x2BB1).is_err());

        // 2020-05-00 - low day
        assert!(DOSDate::try_from(0x28A0).is_err());

        // 2003-02-29 - non-leap year
        assert!(DOSDate::try_from(0x2E5D).is_err());

        // 2100-02-29 - non-leap year, divisible by 100
        assert!(DOSDate::try_from(0xF05D).is_err());
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
        assert_eq!(DOSDate::try_from([0x5D, 0x28]).unwrap(), DOSDate {
            year: 2000,
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
        assert!(DOSDate::try_from([0x02, 0x26]).is_err());

        // 2001-13-17 - high month
        assert!(DOSDate::try_from([0xB1, 0x2B]).is_err());

        // 2020-05-00 - low day
        assert!(DOSDate::try_from([0xA0, 0x28]).is_err());

        // 2003-02-29 - non-leap year
        assert!(DOSDate::try_from([0x5D, 0x2E]).is_err());

        // 2100-02-29 - non-leap year, divisible by 100
        assert!(DOSDate::try_from([0x5D, 0xF0]).is_err());
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
