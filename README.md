# dostime

This crate converts `DOSTime`s, `DOSDate`s, `DOSDateTime`s to and from binary and integer
formats. This crate is no_std compatible.

An explanation of the date and time formats can be found
[here](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-dosdatetimetofiletime),
though the documentation for `DOSTime` and `DOSDate` also includes explantions for the format.

```rust
use dostime::{DOSDate, DOSTime, DOSDateTime};
use dostime::date::DateError;
use dostime::time::TimeError;
use dostime::datetime::DateTimeError;

// Valid dates and times can be constructed.
let date = DOSDate::new(2017, 4, 6).unwrap();           // 2017-04-06
let time = DOSTime::new(13, 24, 54).unwrap();           // 13:24:54
let datetime = DOSDateTime::new(2006, 4, 15, 1, 5, 34); // 2006-04-15 01:05:34

// Invalid dates and times can't be constructed and information about what is invalid is
// returned.
let invalid_month = DOSDate::new(1996, 13, 3).unwrap_err();
assert_eq!(invalid_month, DateError::InvalidMonth);

let invalid_second = DOSTime::new(1, 2, 60).unwrap_err();
assert_eq!(invalid_second, TimeError::InvalidSecond);

let invalid_day = DOSDateTime::new(2001, 4, 31, 6, 13, 12).unwrap_err();
assert_eq!(invalid_day, DateTimeError::DateError(DateError::InvalidDay));

// Dates and times can be converted to and from integers and arrays of bytes.
let int: u16 = date.into();
assert_eq!(int, 0x4A86);
assert_eq!(date, DOSDate::try_from(0x4A86).unwrap());

let bytes: [u8; 2] = time.into();
assert_eq!(bytes, [0x1B, 0x6B]);
assert_eq!(time, DOSTime::try_from([0x1B, 0x6B]).unwrap());
```

## Future Work

- Compatibility with the `chrono` crate.
- Compatibility with the `time` crate.

If anyone thinks of something else that this crate should have or spots any bugs, let me know! I'll
see if I can add it. Alternatively, feel free to submit a pull request (or just fork it). I'll
review and approve it as soon as I can.
