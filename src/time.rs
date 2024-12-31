#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

/// A time in MS-DOS format. Timestamps in the wild will always have an even number of seconds.
/// 
/// MS-DOS times are typically stored as little-endian 2-byte values. The 5 lowest-order bits are
/// half the seconds (ex. a value of 25 corresponds to 50 seconds). The next 6 bits are the minutes
/// and the remaining 5 bits are the hours.
/// 
/// For example, `0x6B1B` (big-endian) is `0b0110101100011011`, which corresponds to 13:24:54. See
/// below for a working out of the conversion.
/// 
/// `0x6B1B` -> `0b0110101100011011` -> `01101 011000 11011` -> `13 24 27` -> `13:24:54`
/// 
/// The functions that convert to and from `u16`s interpret the value as big-endian since that makes
/// the math easier. The functions that convert to and from `[u8; 2]` interpret the value as
/// little-endian since bytes are usually stored as little-endian values.
/// 
/// Not all 2-byte sequences correspond to a valid time. For example, the array `[0x00, 0xC0]`
/// would become the time 24:00:00, which is clearly invalid. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSTime`s can be converted into a valid 2-byte sequence (hence the use
/// of `Into`). 
#[derive(Debug, PartialEq, Eq, Default, Clone, Copy)]
pub struct DOSTime {
    hour: u8,
    minute: u8,
    second: u8,
}

/// A list of possible errors that could happen when constructing a time.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TimeError {
    /// The hour is after 23.
    InvalidHour,
    /// The minute is after 59.
    InvalidMinute,
    /// The second is after 59.
    InvalidSecond,
}

impl DOSTime {
    /// Attempts to create a new instance of a `DOSTime`. If the hour, minute, or second is invalid,
    /// then the creation fails and an error is returned.
    /// 
    /// An hour is invalid if it is 24 or greater. A minute is invalid if it is 60 or greater. A
    /// second is invalid if it is 60 or greater.
    /// 
    /// ```
    /// use dostime::DOSTime;
    /// use dostime::time::TimeError;
    /// 
    /// // Construct valid times.
    /// let time1 = DOSTime::new(0, 0, 0).unwrap();
    /// let time2 = DOSTime::new(15, 21, 19).unwrap();
    /// 
    /// // Invalid times can't be constructed.
    /// let bad_hour = DOSTime::new(24, 12, 1).expect_err("");
    /// assert_eq!(bad_hour, TimeError::InvalidHour);
    /// 
    /// let bad_minute = DOSTime::new(18, 60, 3).expect_err("");
    /// assert_eq!(bad_minute, TimeError::InvalidMinute);
    /// 
    /// let bad_second = DOSTime::new(4, 11, 60).expect_err("");
    /// assert_eq!(bad_second, TimeError::InvalidSecond);
    /// ```
    pub fn new(hour: u8, minute: u8, second: u8) -> Result<Self, TimeError> {
        let time = Self {
            hour,
            minute,
            second,
        };

        if let Err(err) = time.validate() {
            return Err(err);
        }

        Ok(time)
    }

    /// Determines if the time is actually a real time that could be represented by a DOS time. If
    /// the time is invalid, then a `TimeError` is returned.
    fn validate(&self) -> Result<(), TimeError> {
        if self.hour >= 24 {
            return Err(TimeError::InvalidHour);
        }

        if self.minute >= 60 {
            return Err(TimeError::InvalidMinute);
        }

        if self.second >= 60 {
            return Err(TimeError::InvalidSecond);
        }

        return Ok(());
    }
}

impl TryFrom<u16> for DOSTime {
    type Error = TimeError;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        // TODO: 7z seems to always report 2 less than what this calculate to. Why?
        let hour = ((value & 0b1111100000000000) >> 11) as u8;
        let minute = ((value & 0b0000011111100000) >> 5) as u8;
        let second = ((value & 0b0000000000011111) as u8) << 1;

        let time = Self {
            hour,
            minute,
            second,
        };

        if let Err(err) = time.validate() {
            return Err(err);
        }

        Ok(time)
    }
}

impl Into<u16> for DOSTime {
    fn into(self) -> u16 {
        // Shift hour to be last 5 bits of u16
        let hour = (self.hour as u16) << 11;

        // Shift minute to be middle 6 bits of u16
        let minute = (self.minute as u16) << 5;

        // Halve seconds
        let second = (self.second as u16) / 2;

        // Sum hour, minute, and second to create result
        hour + minute + second
    }
}

impl TryFrom<[u8; 2]> for DOSTime {
    type Error = TimeError;

    fn try_from(value: [u8; 2]) -> Result<Self, Self::Error> {
        DOSTime::try_from(u16::from_le_bytes(value))
    }
}

impl Into<[u8; 2]> for DOSTime {
    fn into(self) -> [u8; 2] {
        let bytes: u16 = self.into();
        bytes.to_le_bytes()
    }
}

#[cfg(feature = "std")]
impl Display for DOSTime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:0>2}:{:0>2}:{:0>2}", self.hour, self.minute, self.second)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        // Test detecting if a time is valid

        // Test valid times
        // 00:00:00 - midnight
        let time = DOSTime::new(0, 0, 0).unwrap();
        assert_eq!(time, DOSTime {
            hour: 0,
            minute: 0,
            second: 0
        });

        // 13:24:54
        let time = DOSTime::new(13, 24, 54).unwrap();
        assert_eq!(time, DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        });

        // 23:59:58 - last possible time
        let time = DOSTime::new(23, 59, 58).unwrap();
        assert_eq!(time, DOSTime {
            hour: 23,
            minute: 59,
            second: 58
        });

        // Test invalid times
        // 24:00:00 - high hour
        let error = DOSTime::new(24, 0, 0).unwrap_err();
        assert_eq!(error, TimeError::InvalidHour);

        // 00:60:00 - high minute
        let error = DOSTime::new(0, 60, 0).unwrap_err();
        assert_eq!(error, TimeError::InvalidMinute);

        // 00:00:60 - high second
        let error = DOSTime::new(0, 0, 60).unwrap_err();
        assert_eq!(error, TimeError::InvalidSecond);
    }

    #[test]
    fn test_time_from_u16() {
        // Test converting from a u16 to a DOSTime

        // Test valid times
        // 00:00:00 - midnight
        assert_eq!(DOSTime::try_from(0x0000).unwrap(), DOSTime {
            hour: 0,
            minute: 0,
            second: 0,
        });

        // 13:24:54
        assert_eq!(DOSTime::try_from(0x6B1B).unwrap(), DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        });

        // 23:59:58 - last possible time
        assert_eq!(DOSTime::try_from(0xBF7D).unwrap(), DOSTime {
            hour: 23,
            minute: 59,
            second: 58,
        });

        // Test invalid times
        // 24:00:00 - high hour
        assert_eq!(
            DOSTime::try_from(0xC000).expect_err("High hour allowed."),
            TimeError::InvalidHour
        );

        // 00:60:00 - high minute
        assert_eq!(
            DOSTime::try_from(0x0780).expect_err("High minute allowed."),
            TimeError::InvalidMinute
        );

        // 00:00:60 - high second
        assert_eq!(
            DOSTime::try_from(0x001E).expect_err("High second allowed."),
            TimeError::InvalidSecond
        );
    }

    #[test]
    fn test_time_to_u16() {
        // Test converting to a u16 from a DOSTime

        // 00:00:00 - midnight
        let time: u16 = DOSTime {
            hour: 0,
            minute: 0,
            second: 0,
        }.into();
        assert_eq!(time, 0x0000);

        // 13:24:54
        let time: u16 = DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        }.into();
        assert_eq!(time, 0x6B1B);

        // 23:59:58 - last possible time
        let time: u16 = DOSTime {
            hour: 23,
            minute: 59,
            second: 58,
        }.into();
        assert_eq!(time, 0xBF7D);

        // 06:13:23 - odd seconds (should be impossible)
        let time: u16 = DOSTime {
            hour: 6,
            minute: 13,
            second: 23,
        }.into();
        assert_eq!(time, 0x31AB);
    }

    #[test]
    fn test_time_from_u8arr() {
        // Test converting from a [u8; 2] to a DOSTime

        // Test valid times
        // 00:00:00 - midnight
        assert_eq!(DOSTime::try_from([0x00, 0x00]).unwrap(), DOSTime {
            hour: 0,
            minute: 0,
            second: 0,
        });

        // 13:24:54
        assert_eq!(DOSTime::try_from([0x1B, 0x6B]).unwrap(), DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        });

        // 23:59:58 - last possible time
        assert_eq!(DOSTime::try_from([0x7D, 0xBF]).unwrap(), DOSTime {
            hour: 23,
            minute: 59,
            second: 58,
        });

        // Test invalid times
        // 24:00:00 - high hour
        assert_eq!(
            DOSTime::try_from([0x00, 0xC0]).expect_err("High hour allowed."),
            TimeError::InvalidHour,
        );

        // 00:60:00 - high minute
        assert_eq!(
            DOSTime::try_from([0x80, 0x07]).expect_err("High minute allowed."),
            TimeError::InvalidMinute
        );

        // 00:00:60 - high second
        assert_eq!(
            DOSTime::try_from([0x1E, 0x00]).expect_err("High second allowed."),
            TimeError::InvalidSecond
        );
    }

    #[test]
    fn test_time_to_u8arr() {
        // Test converting to a [u8; 2] from a DOSTime

        // 00:00:00 - midnight
        let time: [u8; 2] = DOSTime {
            hour: 0,
            minute: 0,
            second: 0,
        }.into();
        assert_eq!(time, [0x00, 0x00]);

        // 13:24:54
        let time: [u8; 2] = DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        }.into();
        assert_eq!(time, [0x1B, 0x6B]);

        // 23:59:58 - last possible time
        let time: [u8; 2] = DOSTime {
            hour: 23,
            minute: 59,
            second: 58,
        }.into();
        assert_eq!(time, [0x7D, 0xBF]);

        // 06:13:23 - odd seconds (should be impossible)
        let time: [u8; 2] = DOSTime {
            hour: 6,
            minute: 13,
            second: 23,
        }.into();
        assert_eq!(time, [0xAB, 0x31]);
    }
}
