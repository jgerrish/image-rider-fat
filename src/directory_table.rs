/// Parse a FAT directory table
/// This doesn't include any support for VFAT long filenames or other newer features
use nom::bytes::complete::take;
use nom::number::complete::{le_u16, le_u32, le_u8};
use nom::IResult;
use time::{Date, Month, Time};

use std::fmt::{Display, Formatter, Result};

/// The first byte for a filename can have special values
/// If it is zero, the directory entry is available and there are no further entries
pub enum FileType {
    Normal(FATDirectoryEntry),
    LastEntry,
}

/// TODO: Get these values correct
pub struct FATDirectoryEntry {
    /// offset 0
    /// 8 byte filename, space padded on disk, but without the pads here
    pub filename: String,
    /// offset 3
    /// Three byte file extension
    pub file_extension: String,
    /// offset 11
    /// File attributes for the file
    pub file_attributes: u8,
    /// offset 12
    pub user_attributes: u8,
    /// offset 13
    pub deleted_file_first_character: u8,
    /// offset 14
    /// DR DOS 3.31 password hash
    /// DOS 7.0 create time
    pub create_time: Option<Time>,
    /// offset 16
    /// DOS 7.0 create date
    pub create_date: Option<Date>,
    /// offset 18
    /// Dr DOS 6.0 owner id
    /// DOS 7.0 last access date
    pub last_access_date: Option<Date>,
    /// offset 20
    /// FAT32 first cluster number
    /// FAT12 FAT16 extended attributes handle (first cluster of extended attributes
    /// or zero)
    pub extended_attributes: u16,
    /// offset 22
    pub last_modified_time: Option<Time>,
    /// offset 24
    pub last_modified_date: Option<Date>,
    /// offset 26
    /// start of file in clusters in FAT12 and FAT16
    pub start_of_file: u16,
    /// offset 28
    /// File size in bytes
    /// Entries with Volume Label or Subdirectory flag should be zero
    pub file_size: u32,
}

/// Display an attribute that may be a reserved option
pub fn reserved_time_display(option: Option<Time>) -> String {
    match option {
        Some(s) => format!("{}", s),
        None => "reserved".to_string(),
    }
}

/// Display an attribute that may be a reserved option
pub fn reserved_date_display(option: Option<Date>) -> String {
    match option {
        Some(s) => format!("{}", s),
        None => "reserved".to_string(),
    }
}

impl Display for FATDirectoryEntry {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "filename: {}.{}, ", self.filename, self.file_extension)?;
        write!(
            f,
            "last_create_time: {}, ",
            reserved_time_display(self.create_time)
        )?;
        write!(
            f,
            "last_create_date: {}, ",
            reserved_date_display(self.create_date)
        )?;
        write!(
            f,
            "last_access_date: {}, ",
            reserved_date_display(self.last_access_date)
        )?;
        write!(
            f,
            "last_modified_time: {}, ",
            reserved_time_display(self.last_modified_time)
        )?;
        write!(
            f,
            "last_modified_date: {}, ",
            reserved_date_display(self.last_modified_date)
        )?;
        write!(f, "start_of_file: {}, ", self.start_of_file)?;
        write!(f, "file size: {}", self.file_size)?;
        writeln!(f)
    }
}

/// FAT Directory Table
pub struct FATDirectory {
    /// The directory entries
    pub directory_entries: Vec<FATDirectoryEntry>,
}

impl Display for FATDirectory {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "entries: ")?;
        for entry in &self.directory_entries {
            write!(f, "{}", entry)?;
        }
        writeln!(f)
    }
}

/// TODO: Get these values correct
pub fn fat_directory_entry_parser(i: &[u8]) -> IResult<&[u8], FileType> {
    let (i, filename_padded) = take(8_usize)(i)?;

    if filename_padded[0] == 0 {
        // consume the rest of the directory entry
        let (i, _) = take(24_usize)(i)?;
        return Ok((i, FileType::LastEntry));
    }

    // filenames are encoded in ECMA-6 according to ECMA-107 section 8.5 and section
    // 11.4.1 for filenames
    let filename_result = String::from_utf8(filename_padded.to_vec());
    // If this fails here, it means we have an invalid filesystem
    // fail out if that is the case.
    let filename = match filename_result {
        Ok(s) => s,
        Err(e) => {
            panic!("Invalid filename: {}", e);
            // return Err(Err::Error(nom::error_position!(i, ErrorKind::Fail)));
        }
    };
    let filename = String::from(filename.trim_end_matches(' '));

    let (i, file_extension_padded) = take(3_usize)(i)?;
    let file_extension_result = String::from_utf8(file_extension_padded.to_vec());
    let file_extension = match file_extension_result {
        Ok(s) => s,
        Err(e) => panic!("Invalid file extension: {}", e),
    };
    let file_extension = String::from(file_extension.trim_end_matches(' '));

    let (i, file_attributes) = le_u8(i)?;
    let (i, user_attributes) = le_u8(i)?;
    let (i, deleted_file_first_character) = le_u8(i)?;
    let (i, create_time) = le_u16(i)?;
    let create_time = parse_dos_time(create_time);
    let (i, create_date) = le_u16(i)?;
    let create_date = parse_dos_date(create_date);
    let (i, last_access_date) = le_u16(i)?;
    let last_access_date = parse_dos_date(last_access_date);
    let (i, extended_attributes) = le_u16(i)?;
    let (i, last_modified_time) = le_u16(i)?;
    let last_modified_time = parse_dos_time(last_modified_time);
    let (i, last_modified_date) = le_u16(i)?;
    let last_modified_date = parse_dos_date(last_modified_date);
    let (i, start_of_file) = le_u16(i)?;
    let (i, file_size) = le_u32(i)?;

    let fat_directory_entry = FATDirectoryEntry {
        filename,
        file_extension,
        file_attributes,
        user_attributes,
        deleted_file_first_character,
        create_time,
        create_date,
        last_access_date,
        extended_attributes,
        last_modified_time,
        last_modified_date,
        start_of_file,
        file_size,
    };

    Ok((i, FileType::Normal(fat_directory_entry)))
}

/// Parse a FAT Directory Table
pub fn fat_directory_parser(i: &[u8]) -> IResult<&[u8], FATDirectory> {
    let mut directory_entries = Vec::new();
    let mut stop = false;
    let mut index = i;

    while !stop {
        let (i, directory_entry) = fat_directory_entry_parser(index)?;

        index = i;
        match directory_entry {
            FileType::LastEntry => {
                stop = true;
            }
            FileType::Normal(e) => {
                directory_entries.push(e);
            }
        }
    }

    Ok((index, FATDirectory { directory_entries }))
}

pub fn parse_dos_time(dos_time: u16) -> Option<Time> {
    // Assume a value of zero is an "invalid" time and the field is a
    // "reserved" field
    // This isn't always true, some utilities may not write a time
    if dos_time == 0 {
        return None;
    }

    let hours = ((dos_time >> 11) as u8) & 0x1F;
    let minutes = ((dos_time >> 5) as u8) & 0x3F;
    let seconds = (dos_time & 0x1F) as u8;

    let time = Time::from_hms(hours, minutes, seconds);

    match time {
        Ok(t) => Some(t),
        Err(e) => panic!("Couldn't parse time: {}", e),
    }
}

/// Parse a FAT date
/// Assume a value of zero is an invalid date / reserved field
pub fn parse_dos_date(dos_date: u16) -> Option<Date> {
    // Assume a value of zero is an "invalid" date and the field is a
    // "reserved" field
    // This isn't always true, some utilities may not write a date
    if dos_date == 0 {
        return None;
    }

    let year: i32 = (((dos_date >> 9) & 0x7F) as i32) + 1980;
    let month = (dos_date >> 5) & 0x0f;

    let month = match month {
        1 => Month::January,
        2 => Month::February,
        3 => Month::March,
        4 => Month::April,
        5 => Month::May,
        6 => Month::June,
        7 => Month::July,
        8 => Month::August,
        9 => Month::September,
        10 => Month::October,
        11 => Month::November,
        12 => Month::December,
        what => panic!("Invalid month: {}", what),
    };

    let day = (dos_date & 0x1F) as u8;

    let date = Date::from_calendar_date(year, month, day);

    match date {
        Ok(d) => Some(d),
        Err(e) => panic!("Couldn't parse date: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use super::{fat_directory_entry_parser, fat_directory_parser, FileType};

    /// Test that parsing a FAT12 directory entry works
    #[test]
    fn parse_fat12_directory_entry_works() {
        let image_data: [u8; 32] = [
            0x48, 0x45, 0x4c, 0x4c, 0x4f, 0x20, 0x20, 0x20, 0x43, 0x4f, 0x20, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        let result = fat_directory_entry_parser(&image_data);

        match result {
            Ok((_, res)) => match res {
                FileType::LastEntry => panic!("Should not have zero as first byte"),
                FileType::Normal(de) => {
                    assert_eq!(de.filename, "HELLO");
                    assert_eq!(de.file_extension, "CO");
                }
            },
            Err(e) => panic!("Error parsing FAT12 Directory Entry: {}", e),
        }
    }

    /// Test that parsing a FAT12 last directory entry works
    #[test]
    fn parse_fat12_last_directory_entry_works() {
        let image_data: [u8; 32] = [
            0x00, 0x45, 0x4c, 0x4c, 0x4f, 0x20, 0x20, 0x20, 0x43, 0x4f, 0x20, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        let result = fat_directory_entry_parser(&image_data);

        match result {
            Ok((_i, res)) => match res {
                FileType::LastEntry => {
                    // Making assumptions about addresses being contiguous
                    // and usize size
                    // But it makes sure we're consuming 32 bytes
                    // This may fail on other architectures
                    // assert_eq!(std::ptr::addr_of!(i) as u8 -
                    //            std::ptr::addr_of!(image_data) as u8,
                    //            128,
                    //          );
                    return;
                }
                FileType::Normal(_) => {
                    panic!("Should not be a normal directory entry")
                }
            },
            Err(e) => panic!("Error parsing FAT12 Directory Entry: {}", e),
        }
    }

    /// Test parsing a directory table
    #[test]
    fn parse_fat12_directory_table_works() {
        let image_data: [u8; 64] = [
            // entry one
            0x48, 0x45, 0x4c, 0x4c, 0x4f, 0x20, 0x20, 0x20, 0x43, 0x4f, 0x20, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, // entry two
            0x00, 0x45, 0x4c, 0x4c, 0x4f, 0x20, 0x20, 0x20, 0x43, 0x4f, 0x20, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        let directory_table_result = fat_directory_parser(&image_data);

        match directory_table_result {
            Ok((_i, directory_table)) => {
                assert_eq!(directory_table.directory_entries.len(), 1);
                assert_eq!(directory_table.directory_entries[0].filename, "HELLO");
            }
            Err(e) => panic!("Error parsing directory table: {}", e),
        }
    }
}
