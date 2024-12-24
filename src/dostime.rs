#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

use core::fmt::Display;

/// A time in MS-DOS format. Timestamps will always have an even number of seconds.
/// 
/// MS-DOS times are typically stored as little-endian 2 byte values. The 5 lowest-order bits are
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
/// Not all 2 byte sequences correspond to a valid time. For example, the array `[0x00, 0xC0]`
/// would become the time 24:00:00, which is clearly invalid. This implementation rejects these
/// timestamps and disallows their construction (hence the use of `TryFrom` rather than `From`).
/// However, all possible `DOSTime`s can be converted into a valid 2 byte sequence (hence the use
/// of `Into`). 
#[derive(Debug, PartialEq, Eq, Default, Clone, Copy)]
pub struct DOSTime {
    hour: u8,
    minute: u8,
    second: u8,
}

impl DOSTime {
    // Returns true if the DOSTime represents a possible valid time
    // Ex. 14:03:60 is invalid, 23
    fn is_valid(&self) -> bool {
        if self.hour >= 24 {
            return false;
        }

        if self.minute >= 60 {
            return false;
        }

        if self.second >= 60 {
            return false;
        }

        return true;
    }
}

impl TryFrom<u16> for DOSTime {
    type Error = ();

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

        if !time.is_valid() {
            return Err(());
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
    type Error = ();

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

    impl DOSTime {
        pub fn debug_new(hour: u8, minute: u8, second: u8) -> Self {
            Self {
                hour,
                minute,
                second,
            }
        }
    }

    #[test]
    fn test_is_valid() {
        // Test detecting if a time is valid

        // Test valid times
        // 00:00:00 - midnight
        assert!(DOSTime {
            hour: 0,
            minute: 0,
            second: 0
        }.is_valid());

        // 13:24:54
        assert!(DOSTime {
            hour: 13,
            minute: 24,
            second: 54,
        }.is_valid());

        // 23:59:58 - last possible time
        assert!(DOSTime {
            hour: 23,
            minute: 59,
            second: 58
        }.is_valid());

        // Test invalid times
        // 24:00:00 - high hour
        assert!(!DOSTime {
            hour: 24,
            minute: 0,
            second: 0
        }.is_valid());

        // 00:60:00 - high minute
        assert!(!DOSTime {
            hour: 0,
            minute: 60,
            second: 0
        }.is_valid());

        // 00:00:60 - high second
        assert!(!DOSTime {
            hour: 0,
            minute: 0,
            second: 60,
        }.is_valid());
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
        assert!(DOSTime::try_from(0xC000).is_err());

        // 00:60:00 - high minute
        assert!(DOSTime::try_from(0x0780).is_err());

        // 00:00:60 - high second
        assert!(DOSTime::try_from(0x001E).is_err());
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
        assert!(DOSTime::try_from([0x00, 0xC0]).is_err());

        // 00:60:00 - high minute
        assert!(DOSTime::try_from([0x80, 0x07]).is_err());

        // 00:00:60 - high second
        assert!(DOSTime::try_from([0x1E, 0x00]).is_err());
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
