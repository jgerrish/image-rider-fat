use log::{debug, error};
use nom::bytes::complete::take;
use nom::number::complete::le_u16;
use nom::IResult;

use std::fmt::{Display, Formatter, Result, UpperHex};

use super::fat::FATBootSector;

/// The meanining of entries in the FAT cluster map
#[derive(Clone, Debug, PartialEq)]
pub enum FAT12ClusterEntry {
    /// Indicates a free cluster or or parent cluster starting directory
    /// Valid values: 0x000
    FreeCluster,

    /// Reserved cluster
    /// Used temporarily by file systems during file allocation
    /// Implementations should treat it as end-of-chain marker
    /// Valid values: 0x001
    Reserved1,

    /// Data Cluster
    /// Valid values: 0x002 - 0xFEF
    DataCluster(u16),

    /// Reserved
    /// Valid values: 0xFF0 - 0xFF5
    Reserved2(u16),

    /// Reserved
    /// Valid values: 0xFF6
    Reserved3,

    /// Bad Sector in Cluster Marker
    /// Valid values: 0xFF7
    BadCluster,

    /// End of Chain Marker
    /// Valid values: 0xFF8 - 0xFFF
    EndOfChainMarker(u16),
}

/// Print FAT12 cluster entries as 12-bit hex values
impl UpperHex for FAT12ClusterEntry {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            FAT12ClusterEntry::FreeCluster => write!(f, "000"),
            FAT12ClusterEntry::Reserved1 => write!(f, "001"),
            FAT12ClusterEntry::DataCluster(value) => write!(f, "{:03X}", value),
            FAT12ClusterEntry::Reserved2(value) => write!(f, "{:03X}", value),
            FAT12ClusterEntry::Reserved3 => write!(f, "FF6"),
            FAT12ClusterEntry::BadCluster => write!(f, "FF7"),
            FAT12ClusterEntry::EndOfChainMarker(value) => write!(f, "{:03X}", value),
        }
    }
}

/// Display a FAT12 cluster as a series of characters
// pub fn fat_clusters_as_chars(fat_clusters: Vec<FAT12ClusterEntry>) -> String {
// }

/// Parse a FAT12 value as a FAT12ClusterEntry
pub fn parse_fat12_value(value: u16) -> FAT12ClusterEntry {
    match value {
        0x000 => FAT12ClusterEntry::FreeCluster,
        0x001 => FAT12ClusterEntry::Reserved1,
        0x002..=0xFEF => FAT12ClusterEntry::DataCluster(value),
        0xFF0..=0xFF5 => FAT12ClusterEntry::Reserved2(value),
        0xFF6 => FAT12ClusterEntry::Reserved3,
        0xFF7 => FAT12ClusterEntry::BadCluster,
        0xFF8..=0xFFF => FAT12ClusterEntry::EndOfChainMarker(value),
        4096_u16..=u16::MAX => {
            error!("Invalid FAT12 cluster value: {}", value);
            panic!("Invalid FAT12 cluster value: {}", value);
        }
    }
}

/// A DOS File Allocation Table (FAT)
/// Each two-byte entry in FAT16 is little-endian
#[derive(Debug, PartialEq)]
pub struct FATFAT16 {
    /// The FAT ID
    pub fat_id: u16,
    /// The FAT end-of-cluster-chain marker
    /// Usually 0xFFFF for FAT16, for some Atari ST disks it's 0x03FF
    pub eoc_marker: u16,
    /// The FAT entries / clusters
    pub fat_clusters: Vec<Vec<u16>>,
}

/// Display a File Allocation Table
impl Display for FATFAT16 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "FAT ID: 0x{:X}, ", self.fat_id)?;
        write!(f, "EOC Marker: 0x{:X}, ", self.eoc_marker)?;
        write!(f, "clusters: ")?;
        for chain in &self.fat_clusters {
            write!(f, "new chain: ")?;
            for cluster in chain {
                write!(f, "0x{:X}, ", cluster)?;
            }
            writeln!(f)?;
        }
        writeln!(f)
    }
}

/// Parse a FAT16 File Allocation Table
pub fn fat_fat16_parser<'a>(
    fat_boot_sector: &'a FATBootSector,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATFAT16> + 'a {
    move |i| {
        let (i, fat_id) = le_u16(i)?;
        let (i, eoc_marker) = le_u16(i)?;

        let mut fat_clusters = Vec::new();

        debug!("EOC Marker: {:02X}", eoc_marker);

        let mut cnt = 0;
        let mut index = i;
        let mut fat_entry: u16;
        let max = fat_boot_sector
            .bios_parameter_block
            .bytes_per_logical_sector
            * fat_boot_sector.bios_parameter_block.logical_sectors_per_fat;

        // Note: this depends on integer division truncating the decimal
        let max_truncated = max;

        // parse all max bytes of the FAT
        while cnt < max_truncated {
            let (index_new, fat_entry_new) = le_u16(index)?;
            cnt += 2;
            // There may be a better pattern for this
            fat_entry = fat_entry_new;
            index = index_new;

            let mut chain = Vec::new();
            // read until the EOC marker is found
            while (cnt < max_truncated) && (fat_entry != eoc_marker) {
                chain.push(fat_entry);
                let result = le_u16(index)?;
                cnt += 2;
                index = result.0;
                fat_entry = result.1;
            }
            fat_clusters.push(chain);
        }
        debug!("\nNumber of clusters parsed: {}\n", cnt);

        let (i, _) = take(max_truncated - (cnt + 4))(index)?;

        Ok((
            i,
            FATFAT16 {
                fat_id,
                eoc_marker,
                fat_clusters,
            },
        ))
    }
}

/// A DOS File Allocation Table (FAT)
/// Each two-byte entry in FAT16 is little-endian
#[derive(Debug, PartialEq)]
pub struct FATFAT12 {
    /// The FAT ID
    pub fat_id: u16,
    /// The FAT end-of-cluster-chain marker
    /// Usually 0xFFFF for FAT16, for some Atari ST disks it's 0x03FF
    pub eoc_marker: u16,
    /// The FAT entries / clusters
    pub fat_clusters: Vec<Vec<FAT12ClusterEntry>>,
}

/// Display a File Allocation Table
impl Display for FATFAT12 {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "FAT ID: 0x{:X}, ", self.fat_id)?;
        write!(f, "EOC Marker: 0x{:X}, ", self.eoc_marker)?;
        write!(f, "clusters: ")?;
        for chain in &self.fat_clusters {
            write!(f, "new chain: ")?;
            for cluster in chain {
                write!(f, "0x{:X}, ", cluster)?;
            }
            writeln!(f)?;
        }
        write!(f, "")
    }
}

/// FATType defines the different FAT types
pub enum FATType {
    /// FAT12, 12-bit FAT entries
    FAT12,
    /// FAT16, 16-bit FAT entries
    FAT16,
}

/// Read in the first byte of a fat_header to determine the type
/// TODO: Double check this
// pub fn fat_header_parser(&[u8]) -> IResult<&[u8], FATType>) {

// }

/// Parse a FAT12 File Allocation Table
pub fn fat_fat12_parser<'a>(
    fat_boot_sector: &'a FATBootSector,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATFAT12> + 'a {
    move |i| {
        let (i, res) = little_endian_12_bit_parser(i)?;
        let fat_id = res[0];
        let eoc_marker = res[1];
        // let (i, res) = little_endian_12_bit_parser(i)?;

        // TODO: These aren't correct yet, need to discard remaining four bits, etc.
        // TODO: Also double check the FAT16 code
        // let fat_id = ((res[0] >> 4) & 0xFF) as u8;
        // let eoc_marker = res[1];

        let mut fat_clusters = Vec::new();

        debug!("EOC Marker: {:02X}", eoc_marker);

        let mut cnt = 0;
        let mut index = i;
        let mut fat_entries_new: [u16; 2];

        let max = fat_boot_sector
            .bios_parameter_block
            .bytes_per_logical_sector
            * fat_boot_sector.bios_parameter_block.logical_sectors_per_fat;

        // Note: this depends on integer division truncating the decimal
        let max_truncated = max / 3;

        // parse all max bytes of the FAT
        while cnt < max_truncated {
            // let mut index = index_new;
            let result = little_endian_12_bit_parser(index)?;
            index = result.0;
            fat_entries_new = result.1;
            cnt += 3;
            // There may be a better pattern for this
            let mut fat_entry_1 = parse_fat12_value(fat_entries_new[0]);
            let mut fat_entry_2 = parse_fat12_value(fat_entries_new[1]);

            let mut chain = Vec::new();
            // read until the EOC marker is found or the end of the FAT
            while (cnt < max_truncated)
                && ((fat_entry_1 != FAT12ClusterEntry::EndOfChainMarker(eoc_marker))
                    && (fat_entry_2 != FAT12ClusterEntry::EndOfChainMarker(eoc_marker)))
            {
                chain.push(fat_entry_1);
                chain.push(fat_entry_2);
                let result = little_endian_12_bit_parser(index)?;
                index = result.0;
                fat_entries_new = result.1;
                cnt += 3;
                // index = index_new;

                fat_entry_1 = parse_fat12_value(fat_entries_new[0]);
                fat_entry_2 = parse_fat12_value(fat_entries_new[1]);
            }
            fat_clusters.push(chain);
        }

        let (i, _) = take(max - (cnt + 3))(index)?;

        debug!("Number of clusters parsed: {}", cnt);
        Ok((
            i,
            FATFAT12 {
                fat_id,
                eoc_marker,
                fat_clusters,
            },
        ))
    }
}

/// The actual File Allocation Table in the FAT filesystem
/// This project only supports older filesystems
#[derive(Debug, PartialEq)]
pub enum FAT {
    /// FAT12 File Allocation Table
    FAT12(FATFAT12),
    /// FAT16 File Allocation Table
    FAT16(FATFAT16),
}

/// Parse three bytes into two 12-bit values, little-endian format
/// So 0x12 0x34 0x56 -> 0x0412 0x0563
pub fn little_endian_12_bit_parser(i: &[u8]) -> IResult<&[u8], [u16; 2]> {
    let (i, working_data) = take(3_usize)(i)?;

    // Words are 12-bit words
    let first_word: u16 = (((working_data[1] & 0x0F) as u16) << 8) + (working_data[0] as u16);
    let second_word: u16 =
        ((working_data[2] as u16) << 4) + (((working_data[1] & 0xF0) as u16) >> 4);

    let result: [u16; 2] = [first_word, second_word];

    Ok((i, result))
}

mod tests {
    /// Test parsing 12-bit values
    #[test]
    fn little_endian_12_bit_parser_works() {
        // [0x12, 0x34, 0x56] should parse as [0x0412, 0x0563]
        let data: [u8; 3] = [0x12, 0x34, 0x56];

        let little_endian_12_bit_parser_result = super::little_endian_12_bit_parser(&data);

        match little_endian_12_bit_parser_result {
            Ok((_, result)) => {
                assert_eq!(result[0], 0x0412);
                assert_eq!(result[1], 0x0563);
            }
            Err(_) => panic!("Parser failed"),
        }
    }
}
