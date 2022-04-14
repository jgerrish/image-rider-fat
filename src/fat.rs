/// Parse a MS-DOS FAT filesystem
///
/// These parsing routines will mis-identify data since they're only doing minimal
/// checking right now.
///
/// FAT uses little-endian for all entries in the header,
/// except for some entries in the Atari ST boot sectors
/// The first three bytes are a jump instruction
/// Byte zero is a jump:
/// either a short jump followed by a NOP: 0xEB 0x?? 0x90
/// or a near jump 0xE9 0x?? 0x??
use log::{debug, error};
use nom::bytes::complete::take;
use nom::combinator::verify;
use nom::error::ErrorKind;
use nom::multi::count;
use nom::number::complete::{be_u16, le_u16, le_u8};
use nom::{Err, IResult};

use std::fmt::{Display, Formatter, Result};

use crate::cluster::{fat_fat12_parser, FAT};
use crate::directory_table::{fat_directory_parser, FATDirectory};
use crate::sanity_check::SanityCheck;

/// A DOS FAT disk
pub struct FATDisk<'a> {
    /// The FAT boot sector
    pub fat_boot_sector: FATBootSector<'a>,

    /// The actual File Allocation Table
    pub fat: FAT<'a>,

    /// The backup File Allocation Table
    pub backup_fat: Option<FAT<'a>>,

    /// The root directory table
    pub directory_table: FATDirectory,

    /// The data region of the FAT disk
    pub data_region: &'a [u8],
}

impl SanityCheck for FATDisk<'_> {
    fn check(&self) -> bool {
        match &self.backup_fat {
            Some(fat) => {
                if self.fat != *fat {
                    debug!("FAT should equal backup FAT");
                    false
                } else {
                    true
                }
            }
            None => true,
        }
    }
}

/// Display a DOS FAT disk
impl Display for FATDisk<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.fat_boot_sector)?;
        match &self.fat {
            FAT::FAT12(fat) => write!(f, "{}", fat)?,
            FAT::FAT16(fat) => write!(f, "{}", fat)?,
        }
        write!(f, "root_directory_table: {}", self.directory_table)
    }
}

/// A normal DOS 3.x FAT boot sector
/// Eleven bytes total
pub struct DOS3FATBootSector<'a> {
    /// A three-byte jump instruction and (possible) NOP combination
    pub jump_instruction: u8,
    /// The location to jump to
    /// TODO: This is an unsigned value, double check it's not a relative jump
    pub jump_location: u8,
    /// A single NOP instruction, 0x90
    pub nop_instruction: u8,
    /// eight byte OEM name
    pub oem_name: &'a [u8],
}

impl Display for DOS3FATBootSector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "DOS 3.x FAT Boot Sector: ")?;
        write!(f, "jump_instruction: 0x{:02X}, ", self.jump_instruction)?;
        write!(f, "jump_location: 0x{:02X}, ", self.jump_location)?;
        write!(f, "nop_instruction: 0x{:02X}", self.nop_instruction)
    }
}

/// Perform sanity checks for DOS 2.x boot sectors
impl SanityCheck for DOS3FATBootSector<'_> {
    fn check(&self) -> bool {
        if self.jump_location == 0 {
            debug!(
                "jump_location should be greater than zero: 0x{:02X}",
                self.jump_location
            );
            false
        } else {
            true
        }
    }
}

/// A normal DOS 2.x FAT boot sector
/// Eleven bytes total
pub struct DOS2FATBootSector<'a> {
    /// A three-byte jump instruction (near jump)
    pub jump_instruction: u8,
    /// The location to jump to
    /// TODO: This is an unsigned value.  Figure out if it is a relative jump or not
    pub jump_location: u16,
    /// eight byte OEM name
    pub oem_name: &'a [u8],
}

impl Display for DOS2FATBootSector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "DOS 2.x FAT Boot Sector: ")?;
        write!(f, "jump_instruction: 0x{:02X}, ", self.jump_instruction)?;
        write!(f, "jump_location: 0x{:02X}, ", self.jump_location)
    }
}

/// Perform sanity checks for DOS 2.x boot sectors
impl SanityCheck for DOS2FATBootSector<'_> {
    fn check(&self) -> bool {
        if self.jump_location == 0 {
            debug!(
                "jump_location should be greater than zero: 0x{:02X}",
                self.jump_location
            );
            false
        } else {
            true
        }
    }
}

/// Atari ST FAT Disk Boot Sector
/// Eleven bytes total
pub struct AtariSTFATBootSector<'a> {
    /// 68000 BRA.S instruction (0x60, ...)
    pub jump_instruction: u8,
    /// The location to jump to
    /// TODO: This is an unsigned value, double check it's not a relative jump
    pub jump_location: u8,
    /// six byte OEM name
    pub oem_name: &'a [u8],
    /// three byte serial number
    pub serial_number: &'a [u8],
}

impl Display for AtariSTFATBootSector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "Atari ST FAT Boot Sector: ")?;
        write!(f, "jump_instruction: 0x{:02X}, ", self.jump_instruction)
    }
}

/// Generic FAT Disk Boot Sector
/// TODO: This should be refactored out after the boot sector parsing is refactored
/// Eleven bytes total
pub struct GenericFATBootSector<'a> {
    /// Empty jump instruction (0x00)
    pub jump_instruction: u8,
    /// The empty jump location (0x00)
    pub jump_location: u8,
    /// six byte OEM name
    pub oem_name: &'a [u8],
    /// three byte serial number
    pub serial_number: &'a [u8],
}

impl Display for GenericFATBootSector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "non-bootable Generic FAT Boot Sector: ")?;
        write!(f, "jump_instruction: 0x{:02X}, ", self.jump_instruction)?;
        write!(f, "jump_location: 0x{:02X}, ", self.jump_location)?;
        write!(f, "oem_name: {:?}, ", self.oem_name)?;
        write!(f, "serial_number: {:?}, ", self.serial_number)
    }
}

/// FAT boot sector enum that can contain either a DOS 2.x boot sector or DOS 3.x boot sector
/// TODO: The BIOS Parameter Block actually starts at 0x0B (byte 12), right now these
/// data structures only contain two or three bytes, they should contain eleven bytes
pub enum FATBootSectorStart<'a> {
    /// A DOS3 boot sector (short jump) (also seen on DOS 1.1)
    DOS3(DOS3FATBootSector<'a>),
    /// A DOS2 boot sector (short jump)
    DOS2(DOS2FATBootSector<'a>),
    /// An Atari ST boot sector (starts with 0x60, some values big-endian encoded)
    ST(AtariSTFATBootSector<'a>),

    /// A Generic FAT boot sector
    // TODO: Don't assign this enum until we parse the media descriptor,
    //       need to refactor the parsing
    Generic(GenericFATBootSector<'a>),
}

impl Display for FATBootSectorStart<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FATBootSectorStart::DOS3(bs) => write!(f, "{}", bs),
            FATBootSectorStart::DOS2(bs) => write!(f, "{}", bs),
            FATBootSectorStart::ST(bs) => write!(f, "{}", bs),
            FATBootSectorStart::Generic(bs) => write!(f, "{}", bs),
        }
    }
}

/// The two-byte checksum
/// On Atari ST disks, this is 0x1234 if the disk is bootable
/// On IBM PC systems, this is 0x55 0xAA, it indicates an IBM PC compatible boot
/// sector
pub enum FATBootSectorSignature {
    /// IBM-PC signature is two bytes
    IBMPC([u8; 2]),
    /// Atari ST checksum is big-endian word
    AtariST(u16),
}

/// Display A FATBootSectorSignature
impl Display for FATBootSectorSignature {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FATBootSectorSignature::IBMPC(bytes) => write!(
                f,
                "IBM-PC signature: [0x{:02X}, 0x{:02X}], ",
                bytes[0], bytes[1]
            ),
            FATBootSectorSignature::AtariST(word) => {
                writeln!(f, "Atari ST checksum: 0x{:04x}", word)
            }
        }
    }
}

/// The combined FAT Boot Sector contains the company or version dependent header followed
/// by the BIOS Parameter Block
/// The first eleven bytes are company or version dependent
/// The BIOS Parameter Blocks starts at offset eleven after that
pub struct FATBootSector<'a> {
    /// The BIOS Parameter Block
    pub fat_boot_sector_start: FATBootSectorStart<'a>,
    /// The BIOS Paramter block
    /// Contains information about sector and cluster size and media types
    pub bios_parameter_block: BIOSParameterBlock,
    /// Boot code if there is any, bytes 30-509
    pub boot_code: Option<Vec<u8>>,
    /// The two-byte signature or checksum
    /// On Atari ST disks, this is 0x1234 if the disk is bootable
    /// On IBM PC systems, this is 0x55 0xAA, it indicates an IBM PC compatible boot
    /// sector
    pub signature: FATBootSectorSignature,
}

impl Display for FATBootSector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "boot sector start: {}, ", self.fat_boot_sector_start)?;
        write!(f, "bios_parameter_block: {}, ", self.bios_parameter_block)?;
        write!(
            f,
            "boot_code: {}, ",
            match self.boot_code {
                Some(_) => "yes",
                None => "no",
            }
        )?;
        writeln!(f, "signature: {}", self.signature)
    }
}

/// The Media Descriptor field in the BIOS Parameter Block
/// There is a lot of variability in what each integer value means in this field
/// But the limited number of valid integer values can be used to test for valid FAT images
/*
pub enum MediaDescriptor {
    DrDOSEightInch,
    DrDOSFivePointTwentyFiveInch,
    DrDOSNonStandard,
    DrDOSSuperFloppy,
    ThreePointFiveInch,
    AltosDoubleDensity,
    AltosFixedDisk,
}
*/

/// The BIOS Parameter Block occurs after the first four bytes of the Boot Sector
/// This structure is 13 bytes
pub struct BIOSParameterBlock {
    /// Number of bytes per logical sector, usually 512
    pub bytes_per_logical_sector: u16,
    /// Logical sectors per cluster, valid values are one and powers of two up to and
    /// including 128
    pub logical_sectors_per_cluster: u8,
    /// Count of reserved logical sectors, the number of logical clusters before the first
    /// FAT in the filesystem
    pub count_of_reserved_logical_sectors: u16,
    /// Number of File Allocation Tables, usually two
    pub number_of_fats: u8,
    /// Maximum number of FAT12 or FAT16 root directory entries, or zero for FAT32
    pub maximum_number_of_root_directory_entries: u16,
    /// Total logical sectors, zero for FAT32
    pub total_logical_sectors: u16,
    /// Media Descriptor
    /// Valid values: 0xE5, 0xED, 0xEE, 0xEF, 0xF0, 0xF4, 0xF5, 0xF8, 0xF9, 0xFA
    ///               0xFB, 0xFC, 0xFD, 0xFE, 0xFF
    pub media_descriptor: u8, //MediaDescriptor,
    /// Logical sectors per File Allocation Table for FAT12/FAT16, zero for FAT32
    pub logical_sectors_per_fat: u16,
}

impl Display for BIOSParameterBlock {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "bytes_per_logical_sector: {}, ",
            self.bytes_per_logical_sector
        )?;
        write!(
            f,
            "logical_sectors_per_cluster: {}, ",
            self.logical_sectors_per_cluster
        )?;
        write!(
            f,
            "count_of_reserved_logical_sectors: {}, ",
            self.count_of_reserved_logical_sectors
        )?;
        write!(f, "number_of_fats: {}, ", self.number_of_fats)?;
        write!(
            f,
            "maximum_number_of_root_directory_entries: {}, ",
            self.maximum_number_of_root_directory_entries
        )?;
        write!(f, "total_logical_sectors: {}, ", self.total_logical_sectors)?;
        write!(f, "media_descriptor: 0x{:X}, ", self.media_descriptor)?;
        write!(
            f,
            "logical_sectors_per_fat: {}",
            self.logical_sectors_per_fat
        )
    }
}

/// TODO: Get this parser working as it should
/// e.g. it should fail if there is no NOP for a DOS 3.x
pub fn fat_boot_sector_start_parser(i: &[u8]) -> IResult<&[u8], FATBootSectorStart> {
    let (i, jump_instruction) = le_u8(i)?;

    if jump_instruction == 0xeb {
        // short jump aka normal DOS 3.x disk
        // Assume a little-endian format
        // TODO: Add checks for Atari ST disks and change this
        let (i, jump_location) = le_u8(i)?;
        let (i, nop_instruction) = verify(le_u8, |val: &u8| *val == 0x90)(i)?;
        let (i, oem_name) = take(8_usize)(i)?;

        let fat_boot_sector = DOS3FATBootSector {
            jump_instruction,
            jump_location,
            nop_instruction,
            oem_name,
        };

        if !fat_boot_sector.check() {
            error!("Invalid data");
            panic!("Invalid data");
        }

        Ok((i, FATBootSectorStart::DOS3(fat_boot_sector)))
    } else if jump_instruction == 0xe9 {
        // near jump aka DOS 2.x disk
        // Assume a little-endian format
        // TODO: Add checks for Atari ST disks and change this
        let (i, jump_location) = le_u16(i)?;
        let (i, oem_name) = take(8_usize)(i)?;

        let fat_boot_sector = DOS2FATBootSector {
            jump_instruction,
            jump_location,
            oem_name,
        };

        if !fat_boot_sector.check() {
            error!("Invalid data");
            panic!("Invalid data");
        }

        Ok((i, FATBootSectorStart::DOS2(fat_boot_sector)))
    } else if jump_instruction == 0x60 {
        let (i, jump_location) = le_u8(i)?;
        let (i, oem_name) = take(6_usize)(i)?;
        let (i, serial_number) = take(3_usize)(i)?;

        let fat_boot_sector = AtariSTFATBootSector {
            jump_instruction,
            jump_location,
            oem_name,
            serial_number,
        };

        Ok((i, FATBootSectorStart::ST(fat_boot_sector)))
    } else if jump_instruction == 0x00 {
        // TODO: Refactor with proper NOM conditional parsers
        // TODO: Refactor to include fuller media type information
        // Some disks don't have a jump instruction but are still valid disks
        // they're just not bootable
        // verify there's a valid media descriptor along with some other heuristics
        let (i, jump_location) = le_u8(i)?;
        let (i, oem_name) = take(6_usize)(i)?;
        let (i, serial_number) = take(3_usize)(i)?;

        let fat_boot_sector = GenericFATBootSector {
            jump_instruction,
            jump_location,
            oem_name,
            serial_number,
        };

        Ok((i, FATBootSectorStart::Generic(fat_boot_sector)))
    } else {
        // Unknown jump instruction type
        Err(Err::Error(nom::error_position!(i, ErrorKind::Fail)))
    }
}

/// Parse the entire FAT boot sector, including the start and the BIOS Parameter Block
pub fn fat_boot_sector_parser(
    filesystem_type: &Option<String>,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATBootSector> + '_ {
    move |i| {
        // debug!("inside parser data: {:?}", i);

        let (i, fat_boot_sector_start) = fat_boot_sector_start_parser(i)?;

        debug!("fat_boot_sector_start: {}", fat_boot_sector_start);

        let (i, bios_parameter_block) = bios_parameter_block_parser(i)?;

        debug!("bios_parameter_block: {}", bios_parameter_block);

        // The 6 bytes on an Atari ST are:
        // Number of sectors per track (offset 24-25, usually 9)
        // Number of disk heads (one for single-sided, two for double-sided)
        // Number of hidden sectors (not used on ST)
        // let (i, _) = take(6_usize)(i)?;

        let (i, sectors_per_track) = le_u16(i)?;

        let (i, number_disk_heads) = le_u16(i)?;
        let (i, number_hidden_sectors) = le_u16(i)?;
        // let (_, total_number_sectors) = le_u16(i)?;

        debug!(
            "sectors_per_track: {}, number_disk_heads: {}, number_hidden_sectors: {}\n",
            sectors_per_track, number_disk_heads, number_hidden_sectors
        );

        // debug!("total_number_sectors: {}\n",total_number_sectors);

        // If we found a boot sector start with a jump instruction, parse the boot
        // code
        let (i, boot_code) = take(480_usize)(i)?;

        let boot_code = match fat_boot_sector_start {
            FATBootSectorStart::DOS3(_) => Some(boot_code.to_vec()),
            FATBootSectorStart::DOS2(_) => Some(boot_code.to_vec()),
            FATBootSectorStart::ST(_) => Some(boot_code.to_vec()),
            FATBootSectorStart::Generic(_) => None,
        };

        // The checksum is computed over the "big endian words" of the boot sector,
        // The checksum itself may or may not be big endian
        // Converting to a normal array may be the wrong choice
        // If the filesystem type is explicitly specified, set the signature
        let (i, signature) = if let Some(s) = filesystem_type {
            debug!("\nUgh: {}\n", s);
            match s.as_ref() {
                "AtariST" => {
                    let (i, sig) = be_u16(i)?;
                    (i, FATBootSectorSignature::AtariST(sig))
                }
                "DOS2" => {
                    let (i, sig) = take(2_usize)(i)?;
                    (i, FATBootSectorSignature::IBMPC([sig[0], sig[1]]))
                }
                "DOS3" => {
                    let (i, sig) = take(2_usize)(i)?;
                    (i, FATBootSectorSignature::IBMPC([sig[0], sig[1]]))
                }
                _ => {
                    panic!("Invalid filesystem-type argument");
                }
            }
        } else {
            match fat_boot_sector_start {
                FATBootSectorStart::DOS3(_) => {
                    let (i, sig) = take(2_usize)(i)?;
                    (i, FATBootSectorSignature::IBMPC([sig[0], sig[1]]))
                }
                FATBootSectorStart::DOS2(_) => {
                    let (i, sig) = take(2_usize)(i)?;
                    (i, FATBootSectorSignature::IBMPC([sig[0], sig[1]]))
                }
                FATBootSectorStart::ST(_) => {
                    let (i, sig) = be_u16(i)?;
                    (i, FATBootSectorSignature::AtariST(sig))
                }
                FATBootSectorStart::Generic(_) => {
                    let (i, sig) = take(2_usize)(i)?;
                    (i, FATBootSectorSignature::IBMPC([sig[0], sig[1]]))
                }
            }
        };

        let fat_boot_sector = FATBootSector {
            fat_boot_sector_start,
            bios_parameter_block,
            boot_code,
            signature,
        };

        Ok((i, fat_boot_sector))
    }
}

/// Return true if the value is a valid media descriptor
pub fn verify_media_descriptor(value: &u8) -> bool {
    matches!(
        value,
        0x00 |                  // Seen in some bootable Atari ST images
        0xE5 | 0xED
            | 0xEE
            | 0xEF
            | 0xF0
            | 0xF4
            | 0xF5
            | 0xF8              // Atari ST 80 track SS
            | 0xF9              // Atari ST 80 track DS
            | 0xFA
            | 0xFB
            | 0xFC              // Atari ST 40 track SS
            | 0xFD              // Atari ST 40 track DS
            | 0xFE
            | 0xFF
    )
}

/// Parse the BIOS Parameter Block
pub fn bios_parameter_block_parser(i: &[u8]) -> IResult<&[u8], BIOSParameterBlock> {
    let (i, bytes_per_logical_sector) = le_u16(i)?;
    let (i, logical_sectors_per_cluster) = le_u8(i)?;
    let (i, count_of_reserved_logical_sectors) = le_u16(i)?;
    let (i, number_of_fats) = le_u8(i)?;
    let (i, maximum_number_of_root_directory_entries) = le_u16(i)?;
    let (i, total_logical_sectors) = le_u16(i)?;
    let (i, media_descriptor) = verify(le_u8, verify_media_descriptor)(i)?;
    let (i, logical_sectors_per_fat) = le_u16(i)?;

    let bios_parameter_block = BIOSParameterBlock {
        bytes_per_logical_sector,
        logical_sectors_per_cluster,
        count_of_reserved_logical_sectors,
        number_of_fats,
        maximum_number_of_root_directory_entries,
        total_logical_sectors,
        media_descriptor, //MediaDescriptor::DrDOSNonStandard,
        logical_sectors_per_fat,
    };

    Ok((i, bios_parameter_block))
}

/// Get the 512 bytes of the boot sector as big-endian words (two bytes)
pub fn parse_boot_sector_as_words(sector_data: &[u8]) -> IResult<&[u8], Vec<u16>> {
    count(be_u16, 0x100_usize)(sector_data)
}

/// Return true if this is a boot sector
/// Calculate the sector sum to see if it's a valid boot sector
/// The checksum is calculated over the 256 words of the boot sector
/// These words are in big-endian format
/// STX disks may not have valid boot sectors
/// There are a couple signs a STX disk isn't a boot sector
///   If the boot sector checksum isn't 0x1234
///   If there is no jump in the first byte of the boot sector
pub fn calculate_boot_sector_sum_from_words(sector_data: &[u8]) -> bool {
    let mut sum: u32 = 0;

    let words_result = parse_boot_sector_as_words(sector_data);

    match words_result {
        Ok((_, words)) => {
            for word in words {
                sum = (sum + (word as u32)) % 0xFFFF;
            }
        }
        Err(_) => panic!("Parsing failed for boot sector checksum"),
    }

    sum == 0x1234
}

/// Parse a DOS FAT image
pub fn fat_disk_parser<'a>(
    filesystem_type: &'a Option<String>,
    root_dir_loc: &'a Option<u32>,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATDisk> + 'a {
    move |i| {
        // Read in 512 bytes as 256 big-endian words for the checksum
        // This is also in the main image-rider code
        let (_, _boot_sectors_as_big_endian_words) = parse_boot_sector_as_words(i)?;

        let (i, fat_boot_sector) = fat_boot_sector_parser(filesystem_type)(i)?;

        // Dump the FAT
        debug!("boot sector: {}", fat_boot_sector);

        let fat_sector = fat_boot_sector
            .bios_parameter_block
            .count_of_reserved_logical_sectors;
        let sector_size = fat_boot_sector
            .bios_parameter_block
            .bytes_per_logical_sector;

        // The initial boot sector is 11 bytes, the BPB is 13 bytes
        // We consume the rest as part of the fat_boot_sector_parser
        // So far, we've consumed 512 bytes
        let offset = (sector_size * fat_sector) - 512;
        debug!("Skipping {} bytes to the FAT", offset);

        // Skip to the FAT
        let (i, _) = take(offset)(i)?;

        // TODO: FAT12 or FAT16 should be dynamically determined
        let (i, fat1) = fat_fat12_parser(&fat_boot_sector)(i)?;

        // parse the backup FAT
        let (i, fat2) = if fat_boot_sector.bios_parameter_block.number_of_fats == 2 {
            let (i, res) = fat_fat12_parser(&fat_boot_sector)(i)?;
            (i, Some(FAT::FAT12(res)))
        } else {
            (i, None)
        };

        // Dump the FAT
        debug!("FAT: {}", fat1);

        // skip over bad sectors or find a different way
        let (i, directory_table) = if let Some(location) = root_dir_loc {
            let end_of_fat = i;
            let (i, _) = take(location - 5600 - 32)(i)?;
            // Parse the root directory table
            // This may be wrong if there is a bad sector in the first cluster:
            // https://formats.kaitai.io/vfat/index.html
            let (_i, directory_table) = fat_directory_parser(i)?;
            (end_of_fat, directory_table)
        } else {
            let (i, directory_table) = fat_directory_parser(i)?;
            // Advance beyond the directory table
            let remaining = (fat_boot_sector
                .bios_parameter_block
                .maximum_number_of_root_directory_entries
                * 32) as usize
                - (directory_table.directory_entries.len() * 32);

            let (i, _) = take(remaining)(i)?;
            (i, directory_table)
        };

        // We're in the data region
        // Read in the rest of the data
        let (i, data_region) = take(i.len())(i)?;

        let fat_disk = FATDisk {
            fat_boot_sector,
            fat: FAT::FAT12(fat1),
            backup_fat: fat2,
            directory_table,
            data_region,
        };

        // Run a sanity check on the FAT Disk
        // TODO: Decide where sanity checks should be run, e.g. by the parser or the caller
        // TODO: Verify the code, they appear different
        fat_disk.check();

        Ok((i, fat_disk))
    }
}

#[cfg(test)]
mod tests {
    use super::FATBootSectorStart;
    use super::{
        bios_parameter_block_parser, calculate_boot_sector_sum_from_words, fat_boot_sector_parser,
        fat_boot_sector_start_parser,
    };

    /// Test that parsing a FAT 3 boot sector works
    #[test]
    fn parse_fat3_boot_sector_start_works() {
        let image_data: [u8; 11] = [
            0xeb, 0x5c, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        let fat_boot_sector_parser_result = fat_boot_sector_start_parser(&image_data);
        match fat_boot_sector_parser_result {
            Ok((_, res)) => match res {
                FATBootSectorStart::DOS3(bs) => {
                    assert_eq!(bs.jump_instruction, 0xeb);
                    assert_eq!(bs.jump_location, 0x5c);
                    assert_eq!(bs.nop_instruction, 0x90);
                }
                FATBootSectorStart::DOS2(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::ST(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::Generic(_bs) => panic!("Wrong DOS version parsed"),
            },
            Err(e) => panic!("Error parsing DOS header: {}", e),
        }
    }

    /// Test that parsing a FAT 2.x boot sector works
    #[test]
    fn parse_fat2_boot_sector_start_works() {
        let image_data: [u8; 11] = [
            0xe9, 0xa3, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        let fat_boot_sector_parser_result = fat_boot_sector_start_parser(&image_data);
        match fat_boot_sector_parser_result {
            Ok((_, res)) => match res {
                FATBootSectorStart::DOS3(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::DOS2(bs) => {
                    assert_eq!(bs.jump_instruction, 0xe9);
                    assert_eq!(bs.jump_location, 0x04a3);
                }
                FATBootSectorStart::ST(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::Generic(_bs) => panic!("Wrong DOS version parsed"),
            },
            Err(e) => panic!("Error parsing DOS header: {}", e),
        }
    }

    /// Test that parsing an Atari ST boot sector works
    #[test]
    fn parse_atari_st_boot_sector_start_works() {
        let image_data: [u8; 11] = [
            0x60, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        let fat_boot_sector_parser_result = fat_boot_sector_start_parser(&image_data);
        match fat_boot_sector_parser_result {
            Ok((_, res)) => match res {
                FATBootSectorStart::DOS3(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::DOS2(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::ST(bs) => {
                    assert_eq!(bs.jump_instruction, 0x60);
                }
                FATBootSectorStart::Generic(_bs) => panic!("Wrong DOS version parsed"),
            },
            Err(e) => panic!("Error parsing DOS header: {}", e),
        }
    }

    /// Test that parsing a non-bootable boot sector works
    #[test]
    fn parse_generic_boot_sector_start_works() {
        let image_data: [u8; 11] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        let fat_boot_sector_parser_result = fat_boot_sector_start_parser(&image_data);
        match fat_boot_sector_parser_result {
            Ok((_, res)) => match res {
                FATBootSectorStart::DOS3(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::DOS2(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::ST(_bs) => panic!("Wrong DOS version parsed"),
                FATBootSectorStart::Generic(bs) => {
                    assert_eq!(bs.jump_instruction, 0x00);
                    assert_eq!(bs.jump_location, 0x00);
                }
            },
            Err(e) => panic!("Error parsing DOS header: {}", e),
        }
    }

    /// Test that parsing a valid media descriptor fails
    #[test]
    fn valid_media_descriptor_passes() {
        let bios_parameter_block: [u8; 13] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFC, 0x00, 0x00,
        ];

        let bios_parameter_block_parser_result = bios_parameter_block_parser(&bios_parameter_block);

        match bios_parameter_block_parser_result {
            Ok((_, _)) => assert_eq!(true, true),
            Err(_) => panic!("Invalid BIOS Parameter Block"),
        }
    }

    /// Test that parsing an invalid media descriptor fails
    #[test]
    #[should_panic(expected = "Invalid BIOS Parameter Block")]
    fn invalid_media_descriptor_fails() {
        let bios_parameter_block: [u8; 13] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xBB, 0x00, 0x00,
        ];

        let bios_parameter_block_parser_result = bios_parameter_block_parser(&bios_parameter_block);

        match bios_parameter_block_parser_result {
            Ok((_, _)) => assert_eq!(true, true),
            Err(_) => panic!("Invalid BIOS Parameter Block"),
        }
    }

    /// Test that parsing a non-bootable disk with a valid media descriptor passes
    #[test]
    fn valid_generic_media_descriptor_passes() {
        let mut image_data = [0; 512];

        image_data[21] = 0xFC;

        let fat_disk_parser_result = fat_boot_sector_parser(&None)(&image_data);

        match fat_disk_parser_result {
            Ok((_i, _result)) => {
                assert!(true);
            }
            Err(_) => panic!("Invalid BIOS Parameter Block"),
        }
    }

    /// Test that parsing a non-bootable disk with an invalid media descriptor fails
    #[test]
    #[should_panic(expected = "Invalid BIOS Parameter Block")]
    fn invalid_generic_media_descriptor_fails() {
        let image_data: [u8; 24] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xBB, 0x00, 0x00,
        ];

        let fat_disk_parser_result = fat_boot_sector_parser(&None)(&image_data);

        match fat_disk_parser_result {
            Ok((_, _)) => assert_eq!(true, true),
            Err(_) => panic!("Invalid BIOS Parameter Block"),
        }
    }

    /// Test parsing an Atari ST boot sector checksum
    #[test]
    fn stx_boot_sector_checksum_works() {
        let mut boot_sector = [0_u8; 512];

        boot_sector[0] = 0x12;
        boot_sector[1] = 0x34;

        let checksum = calculate_boot_sector_sum_from_words(&boot_sector);

        assert_eq!(checksum, true);
    }
}
