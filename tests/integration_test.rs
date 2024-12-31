use dostime::{DOSDate, DOSDateTime, DOSTime};
#[cfg(feature = "time-1")]
use time::{Date, Month, PrimitiveDateTime, Time};
#[cfg(feature = "chrono-1")]
use chrono::{Datelike, NaiveDate, NaiveDateTime, NaiveTime, Timelike};

#[test]
fn test_datetime() {
    // 2017-04-06
    let bytes = [0x86, 0x4A];
    let date = DOSDate::try_from(bytes).unwrap();

    assert_eq!(date.year(), 2017);
    assert_eq!(date.month(), 4);
    assert_eq!(date.day(), 6);

    let int = u16::from(date);

    assert_eq!(int, 0x4A86);

    // 13:24:54
    let bytes = [0x1B, 0x6B];
    let time = DOSTime::try_from(bytes).unwrap();

    assert_eq!(time.hour(), 13);
    assert_eq!(time.minute(), 24);
    assert_eq!(time.second(), 54);

    let int = u16::from(time);
    
    assert_eq!(int, 0x6B1B);

    let datetime = DOSDateTime::from((date, time));

    assert_eq!(datetime.year(), 2017);
    assert_eq!(datetime.month(), 4);
    assert_eq!(datetime.day(), 6);
    assert_eq!(datetime.hour(), 13);
    assert_eq!(datetime.minute(), 24);
    assert_eq!(datetime.second(), 54);

    let bytes = <[u8; 4]>::from(datetime);

    assert_eq!(bytes, [0x1B, 0x6B, 0x86, 0x4A]);

    let int = u32::from(datetime);

    assert_eq!(int, 0x4A86_6B1B);
}

#[test]
#[cfg(feature = "time-1")]
fn test_to_time_crate() {
    // 2017-04-06
    let ddate = DOSDate::new(2017, 4, 6).unwrap();
    let tdate = Date::from(ddate);

    assert_eq!(tdate.year(), 2017);
    assert_eq!(tdate.month(), Month::April);
    assert_eq!(tdate.day(), 6);

    // 13:24:54
    let dtime = DOSTime::new(13, 24, 54).unwrap();
    let ttime = Time::from(dtime);

    assert_eq!(ttime.hour(), 13);
    assert_eq!(ttime.minute(), 24);
    assert_eq!(ttime.second(), 54);

    let ddatetime = DOSDateTime::from((ddate, dtime));
    let tdatetime = PrimitiveDateTime::from(ddatetime);

    assert_eq!(tdatetime.year(), 2017);
    assert_eq!(tdatetime.month(), Month::April);
    assert_eq!(tdatetime.day(), 6);
    assert_eq!(tdatetime.hour(), 13);
    assert_eq!(tdatetime.minute(), 24);
    assert_eq!(tdatetime.second(), 54);
}

#[test]
#[cfg(feature = "time-1")]
fn test_from_time_crate() {
    // 2017-04-06
    let tdate = Date::from_calendar_date(2017, Month::April, 6).unwrap();
    let ddate = DOSDate::try_from(tdate).unwrap();

    assert_eq!(ddate.year(), 2017);
    assert_eq!(ddate.month(), 4);
    assert_eq!(ddate.day(), 6);

    // 13:24:54
    let ttime = Time::from_hms(13, 24, 54).unwrap();
    let dtime = DOSTime::try_from(ttime).unwrap();

    assert_eq!(dtime.hour(), 13);
    assert_eq!(dtime.minute(), 24);
    assert_eq!(dtime.second(), 54);

    let tdatetime = PrimitiveDateTime::new(tdate, ttime);
    let ddatetime = DOSDateTime::try_from(tdatetime).unwrap();

    assert_eq!(ddatetime.year(), 2017);
    assert_eq!(ddatetime.month(), 4);
    assert_eq!(ddatetime.day(), 6);
    assert_eq!(ddatetime.hour(), 13);
    assert_eq!(ddatetime.minute(), 24);
    assert_eq!(ddatetime.second(), 54);
}

#[test]
#[cfg(feature = "chrono-1")]
fn test_to_chrono_crate() {
    // 2017-04-06
    let ddate = DOSDate::new(2017, 4, 6).unwrap();
    let tdate = NaiveDate::from(ddate);

    assert_eq!(tdate.year(), 2017);
    assert_eq!(tdate.month(), 4);
    assert_eq!(tdate.day(), 6);

    // 13:24:54
    let dtime = DOSTime::new(13, 24, 54).unwrap();
    let ttime = NaiveTime::from(dtime);

    assert_eq!(ttime.hour(), 13);
    assert_eq!(ttime.minute(), 24);
    assert_eq!(ttime.second(), 54);

    let ddatetime = DOSDateTime::from((ddate, dtime));
    let tdatetime = NaiveDateTime::from(ddatetime);

    assert_eq!(tdatetime.year(), 2017);
    assert_eq!(tdatetime.month(), 4);
    assert_eq!(tdatetime.day(), 6);
    assert_eq!(tdatetime.hour(), 13);
    assert_eq!(tdatetime.minute(), 24);
    assert_eq!(tdatetime.second(), 54);
}

#[test]
#[cfg(feature = "chrono-1")]
fn test_from_chrono_crate() {
    // 2017-04-06
    let tdate = NaiveDate::from_ymd_opt(2017, 4, 6).unwrap();
    let ddate = DOSDate::try_from(tdate).unwrap();

    assert_eq!(ddate.year(), 2017);
    assert_eq!(ddate.month(), 4);
    assert_eq!(ddate.day(), 6);

    // 13:24:54
    let ttime = NaiveTime::from_hms_opt(13, 24, 54).unwrap();
    let dtime = DOSTime::try_from(ttime).unwrap();

    assert_eq!(dtime.hour(), 13);
    assert_eq!(dtime.minute(), 24);
    assert_eq!(dtime.second(), 54);

    let tdatetime = NaiveDateTime::new(tdate, ttime);
    let ddatetime = DOSDateTime::try_from(tdatetime).unwrap();

    assert_eq!(ddatetime.year(), 2017);
    assert_eq!(ddatetime.month(), 4);
    assert_eq!(ddatetime.day(), 6);
    assert_eq!(ddatetime.hour(), 13);
    assert_eq!(ddatetime.minute(), 24);
    assert_eq!(ddatetime.second(), 54);
}
