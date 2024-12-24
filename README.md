# dostime
This crate converts Microsoft DOS timestamps to and from binary/integer formats and structs. This
crate is optionally no_std compatible (removing the "std" feature). An explanation of the date and
time formats can be found
[here](https://learn.microsoft.com/en-us/windows/win32/api/winbase/nf-winbase-dosdatetimetofiletime),
though the documentation for `DOSTime` and `DOSDate` also includes explantions for the format. By
default, this crate treats integers as big-endian and arrays as little-endian. In the future,
support for treating arrays as big-endian will be added.

## Future Features
- Add explicit big-endian and little-endian methods for conversion (ex. `try_into_le` and
`try_into_be`)
- Add support for Serde
- Other cool features as I think of them (or as people open issues)