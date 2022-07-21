#![warn(missing_docs)]
#![warn(unsafe_code)]
//! File Allocation Table Cluster and Cluster Entry structures and functions
use log::{debug, error};
use nom::bytes::complete::take;
use nom::number::complete::le_u16;
use nom::IResult;

use std::{
    collections::HashMap,
    fmt::{Display, Formatter, Result, UpperHex},
};

use super::fat::FATBootSector;

/// The meaning of entries in the FAT cluster map
#[derive(Clone, Copy, Debug, PartialEq)]
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

/// Display a FAT12ClusterEntry
impl Display for FAT12ClusterEntry {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            FAT12ClusterEntry::FreeCluster => write!(f, "F"),
            FAT12ClusterEntry::Reserved1 => write!(f, "R"),
            FAT12ClusterEntry::DataCluster(_value) => write!(f, "D"),
            FAT12ClusterEntry::Reserved2(_value) => write!(f, "R"),
            FAT12ClusterEntry::Reserved3 => write!(f, "R"),
            FAT12ClusterEntry::BadCluster => write!(f, "B"),
            FAT12ClusterEntry::EndOfChainMarker(_value) => write!(f, "E"),
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

/// TODO: Find correct values
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FAT16ClusterEntry {
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
impl UpperHex for FAT16ClusterEntry {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            FAT16ClusterEntry::FreeCluster => write!(f, "000"),
            FAT16ClusterEntry::Reserved1 => write!(f, "001"),
            FAT16ClusterEntry::DataCluster(value) => write!(f, "{:03X}", value),
            FAT16ClusterEntry::Reserved2(value) => write!(f, "{:03X}", value),
            FAT16ClusterEntry::Reserved3 => write!(f, "FF6"),
            FAT16ClusterEntry::BadCluster => write!(f, "FF7"),
            FAT16ClusterEntry::EndOfChainMarker(value) => write!(f, "{:03X}", value),
        }
    }
}

/// Parse a FAT16 value as a FAT16ClusterEntry
pub fn parse_fat16_value(value: u16) -> FAT16ClusterEntry {
    match value {
        0x0000 => FAT16ClusterEntry::FreeCluster,
        0x0001 => FAT16ClusterEntry::Reserved1,
        0x0002..=0xFFEF => FAT16ClusterEntry::DataCluster(value),
        0xFFF0..=0xFFF5 => FAT16ClusterEntry::Reserved2(value),
        0xFFF6 => FAT16ClusterEntry::Reserved3,
        0xFFF7 => FAT16ClusterEntry::BadCluster,
        0xFFF8..=0xFFFF => FAT16ClusterEntry::EndOfChainMarker(value),
    }
}

/// A DOS File Allocation Table (FAT)
/// Each two-byte entry in FAT16 is little-endian
#[derive(Debug, PartialEq)]
pub struct FATFAT16<'a> {
    /// The FAT ID
    pub fat_id: u16,

    /// The FAT end-of-cluster-chain marker
    /// Usually 0xFFFF for FAT16, for some Atari ST disks it's 0x03FF
    pub eoc_marker: u16,

    /// The FAT entries / clusters
    /// These are in disk order, not chain order.  To use these cluster chains
    /// You need to walk the chain, finding the next cluster with the current value
    pub fat_clusters: Vec<Vec<FAT16ClusterEntry>>,

    /// An index into the FAT chains
    /// The index key is the start of the chain, the value is a reference to the chain
    /// To build a file or directory, read in starting at the file start and then
    /// look up the next chain by adding two to the start file location
    pub fat_cluster_index: HashMap<u16, usize>,

    /// The raw cluster data
    /// Figure out how to name the IntoIterators and other support for this
    /// The fat_cluster_index isn't needed with this
    /// The raw_data includes all the File Allocation Table data, including the
    /// FAT ID and EOC marker
    pub raw_data: &'a [u8],
}

/// Display a 16-bit File Allocation Table
impl<'a> Display for FATFAT16<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "FAT ID: 0x{:X}, ", self.fat_id)?;
        write!(f, "EOC Marker: 0x{:X}, ", self.eoc_marker)?;
        write!(f, "clusters: ")?;
        for (chain_number, chain) in self.fat_clusters.iter().enumerate() {
            write!(f, "chain 0x{:X}: ", chain_number)?;
            for cluster in chain {
                write!(f, "0x{:X}, ", cluster)?;
            }
            writeln!(f)?;
        }
        writeln!(f)
    }
}

/// Returns true if this cluster chain entry is considered an
/// end-of-chain.
pub fn fat16_cluster_entry_eoc(fat_cluster_entry: FAT16ClusterEntry) -> bool {
    matches!(
        fat_cluster_entry,
        FAT16ClusterEntry::EndOfChainMarker(_) | FAT16ClusterEntry::FreeCluster
    )
}

/// Parse a FAT16 File Allocation Table
pub fn fat_fat16_parser<'a>(
    fat_boot_sector: &'a FATBootSector,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATFAT16> + 'a {
    move |i| {
        let mut cnt = 0;
        let start_index = i;

        let (i, fat_id) = le_u16(i)?;
        cnt += 2;
        let (i, eoc_marker) = le_u16(i)?;
        cnt += 2;

        let mut fat_clusters = Vec::new();

        let mut index = i;
        let mut fat_entry: FAT16ClusterEntry;
        let max = fat_boot_sector
            .bios_parameter_block
            .bytes_per_logical_sector as u32
            * fat_boot_sector.bios_parameter_block.logical_sectors_per_fat as u32;

        // parse all max bytes of the FAT
        while cnt < max {
            let (index_new, fat_entry_new) = le_u16(index)?;
            cnt += 2;
            // There may be a better pattern for this
            fat_entry = parse_fat16_value(fat_entry_new);
            // fat_entry = fat_entry_new;
            index = index_new;

            let mut chain = Vec::new();
            // read until the EOC marker is found
            while (cnt < max) && !fat16_cluster_entry_eoc(fat_entry) {
                chain.push(fat_entry);
                let result = le_u16(index)?;
                cnt += 2;
                index = result.0;
                fat_entry = parse_fat16_value(result.1);
            }
            if !chain.is_empty() {
                fat_clusters.push(chain);
            }
        }

        // Build the cluster index
        let fat_cluster_index = HashMap::new();

        let (_, raw_data) = take(max)(start_index)?;

        Ok((
            index,
            FATFAT16 {
                fat_id,
                eoc_marker,
                fat_clusters,
                fat_cluster_index,
                raw_data,
            },
        ))
    }
}

/// A DOS File Allocation Table (FAT)
/// Each two-byte entry in FAT16 is little-endian
#[derive(Debug, PartialEq)]
pub struct FATFAT12<'a> {
    /// The FAT ID
    pub fat_id: u16,
    /// The FAT end-of-cluster-chain marker
    /// For FAT12, 0xFFF is common
    pub eoc_marker: u16,

    /// The FAT entries / clusters
    /// These are in disk order, not chain order.
    /// To use these cluster chains,
    /// You need to walk the chain, finding the next cluster with the current value
    ///
    pub fat_clusters: Vec<Vec<FAT12ClusterEntry>>,

    /// An index into the FAT chains
    /// The index key is the start of the chain, the value is a reference to the chain
    /// To build a file or directory, read in starting at the file start and then
    /// look up the next chain by converting the file location start to a cluster number
    /// Once you have the cluster number, walk the cluster chain to find the next cluster
    /// entry.
    pub fat_cluster_index: HashMap<u16, usize>,

    /// The raw cluster data
    /// Figure out how to name the IntoIterators and other support for this
    /// The fat_cluster_index isn't needed with this
    /// The raw_data includes all the File Allocation Table data, including the
    /// FAT ID and EOC marker
    pub raw_data: &'a [u8],
}

/// Display a File Allocation Table
impl<'a> Display for FATFAT12<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "FAT ID: 0x{:X}, ", self.fat_id)?;
        write!(f, "EOC Marker: 0x{:X}, ", self.eoc_marker)?;
        write!(f, "clusters: ")?;
        for (chain_number, chain) in self.fat_clusters.iter().enumerate() {
            write!(f, "chain {}: ", chain_number)?;
            for cluster in chain {
                write!(f, "0x{:X}, ", cluster)?;
            }
            writeln!(f)?;
        }
        write!(f, "")
    }
}

/// Convert from FAT12ClusterEntry to 12-bit value
pub fn fat12_cluster_entry_to_12_bit_value(cluster_entry: FAT12ClusterEntry) -> u16 {
    match cluster_entry {
        FAT12ClusterEntry::FreeCluster => 0x000,
        FAT12ClusterEntry::Reserved1 => 0x001,
        FAT12ClusterEntry::DataCluster(d) => d,
        FAT12ClusterEntry::Reserved2(d) => d,
        FAT12ClusterEntry::Reserved3 => 0xFF6,
        FAT12ClusterEntry::BadCluster => 0xFF7,
        FAT12ClusterEntry::EndOfChainMarker(d) => d,
    }
}

/// Convert a vector of FAT12ClusterEntry values to Vec<u8> raw byte
/// data.  This can be used to serialize the data to disk
pub fn fat12_cluster_entries_to_u8_vec(cluster: std::vec::Vec<FAT12ClusterEntry>) -> Vec<u8> {
    let mut data: Vec<u8> = Vec::new();

    let mut iter = cluster.iter();

    while let Some(x1) = iter.next() {
        let word1 = fat12_cluster_entry_to_12_bit_value(*x1);
        let word2 = match iter.next() {
            // TODO: This can be done with a map
            Some(x2) => fat12_cluster_entry_to_12_bit_value(*x2),
            None => 0x000,
        };
        // We have one or two 12-bit words, we need to put them in
        // three bytes.
        // e.g.: (0x412, 0x563) -> (0x12, 0x34, 0x56)
        let bytes: [u8; 3] = [
            (word1 & 0xFF).try_into().unwrap(),
            ((word1 >> 8) & ((word2 & 0x0F) << 4)).try_into().unwrap(),
            (word2 >> 4).try_into().unwrap(),
        ];
        data.copy_from_slice(&bytes);
    }

    data
}

/// FATType defines the different FAT types
pub enum FATType {
    /// FAT12, 12-bit FAT entries
    FAT12,
    /// FAT16, 16-bit FAT entries
    FAT16,
}

/// Display a File Allocation Table Type
impl Display for FATType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FATType::FAT12 => write!(f, "FAT12"),
            FATType::FAT16 => write!(f, "FAT16"),
        }
    }
}

/// Structure to hold iterator state for iterating from bytes to 12-bit words
pub struct Into12BitWordIter<'a> {
    /// The data to generate the iterator from.
    pub data: &'a [u8],
    /// Index of the current posiition in the data.
    pub index: usize,
    /// temporary data needed since we're parsing groups of bytes into
    /// 12-bit words.
    pub temp: Option<u16>,
}

/// IntoIterator implementation to create an iterator from bytes to 12-bit words
impl<'a> IntoIterator for FATFAT12<'a> {
    type Item = u16;
    type IntoIter = Into12BitWordIter<'a>;

    /// Build an iterator for this cluster chain
    fn into_iter(self) -> Self::IntoIter {
        Into12BitWordIter {
            data: self.raw_data,
            index: 3,
            temp: None,
        }
    }
}

impl<'a> FATFAT12<'a> {
    /// Build an iterator for this cluster chain
    /// The iteration starts at cluster number cluster
    pub fn into_iter_from_cluster(self, cluster: usize) -> Into12BitWordIter<'a> {
        if (cluster % 2) == 0 {
            // This is the easy case, just go to the index, no intermediate value
            Into12BitWordIter {
                data: self.raw_data,
                index: ((cluster / 2) * 3) + 3,
                temp: None,
            }
        } else {
            // Build the intermediate value and point to the index
            let data = self.raw_data;
            let mut index = (((cluster - 1) / 2) * 3) + 3;
            if index < (data.len() - 2) {
                let data = &data[index..index + 3];
                index += 3;
                let result = little_endian_12_bit_parser(data);
                match result {
                    Ok(res) => Into12BitWordIter {
                        data: self.raw_data,
                        index,
                        temp: Some(res.1[1]),
                    },
                    Err(e) => {
                        panic!("Error parsing 12-bit value: {}", e);
                    }
                }
            } else {
                Into12BitWordIter {
                    data: self.raw_data,
                    index: self.raw_data.len(),
                    temp: None,
                }
            }
        }
    }
}

/// First-level iterator, go from a little-endian 8-bit slice to individual 12-bit words
impl Iterator for Into12BitWordIter<'_> {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        if self.temp.is_some() {
            let value = self.temp;
            self.temp = None;
            value
        } else if self.index < self.data.len() - 2 {
            let data = &self.data[self.index..self.index + 3];
            self.index += 3;
            let result = little_endian_12_bit_parser(data);
            match result {
                Ok(res) => {
                    self.temp = Some(res.1[1]);
                    Some(res.1[0])
                }
                Err(e) => {
                    debug!("Error parsing 12-bit value: {}", e);
                    None
                }
            }
        } else {
            None
        }
    }
}

/// The data structure to iterate through cluster entries
// TODO: Rename some of these iterator structures, can be integrated elsewhere
pub struct FAT12ClusterChain<'a> {
    /// End of Chain marker for this cluster chain
    pub eoc_marker: u16,
    /// The raw cluster data
    /// TODO: Decide on the preferred interface
    /// TODO: Another approach may be to use nom and keep track of the
    /// "i" value as the pointer
    pub raw_data: &'a [u16],
}

/// The iterator state structure for iterating from 12-bit words to FAT12ClusterEntry values
pub struct IntoFAT12ClusterChainIter<'a> {
    /// The cluster chain entries to generate the iterator from.
    pub data: &'a [u16],
    /// index of the current position in the data.
    pub index: usize,
    /// The EOC marker for this FAT.
    pub eoc_marker: u16,
}

impl<'a> IntoIterator for FAT12ClusterChain<'a> {
    type Item = FAT12ClusterEntry;
    type IntoIter = IntoFAT12ClusterChainIter<'a>;

    /// Build an iterator for this cluster chain
    fn into_iter(self) -> IntoFAT12ClusterChainIter<'a> {
        IntoFAT12ClusterChainIter {
            data: self.raw_data,
            index: 0,
            eoc_marker: 0xFFF,
        }
    }
}

impl<'a> FAT12ClusterChain<'a> {
    /// Build an iterator for this cluster chain
    /// The iteration starts at cluster number cluster
    pub fn into_iter_from_cluster(self, cluster: usize) -> IntoFAT12ClusterChainIter<'a> {
        IntoFAT12ClusterChainIter {
            data: self.raw_data,
            index: cluster,
            eoc_marker: 0xFFF,
        }
    }
}

/// Second-level iterator, from 12-byte words to FAT12ClusterEntries
impl Iterator for IntoFAT12ClusterChainIter<'_> {
    type Item = FAT12ClusterEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if (self.index < self.data.len())
            && (self.data[self.index] != self.eoc_marker)
            // FreeCluster is also considered EOC marker in cluster chains
            && (self.data[self.index] != 0x00)
        {
            let item = self.data[self.index];
            self.index += 1;
            Some(parse_fat12_value(item))
        } else {
            None
        }
    }
}

/// Returns true if this cluster chain entry is considered an
/// end-of-chain.
pub fn fat12_cluster_entry_eoc(fat_cluster_entry: FAT12ClusterEntry) -> bool {
    matches!(
        fat_cluster_entry,
        FAT12ClusterEntry::EndOfChainMarker(_) | FAT12ClusterEntry::FreeCluster
    )
}

/// Parse a FAT12 File Allocation Table
/// TODO: This can be refactored using the new iterators
///       or a supplementary interface can be supplied
pub fn fat_fat12_parser<'a>(
    fat_boot_sector: &'a FATBootSector,
) -> impl Fn(&[u8]) -> IResult<&[u8], FATFAT12> + 'a {
    move |i| {
        let start_index = i;
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
            // TODO: Refactor this code into an iterator chain:
            // First iterator returns FAT12ClusterEntries from u8 data
            // (one at a time, storing the intermediate result)
            // Second iterator iterates from a starting chain entry to the end of that chain
            // Need the starting chain id / sector id for each chain somehow, either
            // storing the full &[u8] data, or augmenting the data with a start marker
            while (cnt < max_truncated)
                && !(fat12_cluster_entry_eoc(fat_entry_1))
                && !(fat12_cluster_entry_eoc(fat_entry_2))
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
            if !chain.is_empty() {
                fat_clusters.push(chain);
            }
        }

        let (i, _) = take(max - (cnt + 3))(index)?;

        debug!("Number of clusters parsed: {}", cnt);
        // Build the cluster index
        let mut fat_cluster_index = HashMap::new();
        // Using an index iterator instead of references here
        // TODO: redo this as a reference
        // Right now, this is a read-only filesystem crate,
        // but this should be cleaned up.
        for (index, cluster) in fat_clusters.iter().enumerate() {
            if let Some(FAT12ClusterEntry::DataCluster(d)) = cluster.first() {
                fat_cluster_index.insert(*d, index);
            }
        }

        let (_, raw_data) = take(max)(start_index)?;

        Ok((
            i,
            FATFAT12 {
                fat_id,
                eoc_marker,
                fat_clusters,
                fat_cluster_index,
                raw_data,
            },
        ))
    }
}

/// Structure to hold iterator state for iterating from bytes to 16-bit words
pub struct Into16BitWordIter<'a> {
    /// The data to generate the iterator from.
    pub data: &'a [u8],
    /// Index of the current posiition in the data.
    pub index: usize,
}

/// IntoIterator implementation to create an iterator from bytes to 16-bit words
impl<'a> IntoIterator for FATFAT16<'a> {
    type Item = u16;
    type IntoIter = Into16BitWordIter<'a>;

    /// Build an iterator for this cluster chain
    fn into_iter(self) -> Self::IntoIter {
        Into16BitWordIter {
            data: self.raw_data,
            index: 6,
        }
    }
}

impl<'a> FATFAT16<'a> {
    /// Build an iterator for this cluster chain
    /// The iteration starts at cluster number cluster
    pub fn into_iter_from_cluster(self, cluster: usize) -> Into16BitWordIter<'a> {
        // This is the easy case, just go to the index, no intermediate value
        Into16BitWordIter {
            data: self.raw_data,
            index: (cluster * 2) + 6,
        }
    }
}

/// First-level iterator, go from a little-endian 8-bit slice to individual 12-bit words
impl Iterator for Into16BitWordIter<'_> {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.data.len() {
            let data = &self.data[self.index..self.index + 2];
            self.index += 2;
            let result = little_endian_16_bit_parser(data);
            match result {
                Ok(res) => Some(res.1),
                Err(e) => {
                    error!("Couldn't parse FAT16 word: {}", e);
                    panic!("Couldn't parse FAT16 word: {}", e);
                }
            }
        } else {
            None
        }
    }
}

/// The data structure to iterate through cluster entries
// TODO: Rename some of these iterator structures, can be integrated elsewhere
pub struct FAT16ClusterChain<'a> {
    /// End of Chain marker for this cluster chain
    pub eoc_marker: u16,
    /// The raw cluster data
    /// TODO: Decide on the preferred interface
    /// TODO: Another approach may be to use nom and keep track of the
    /// "i" value as the pointer
    pub raw_data: &'a [u16],
}

/// The iterator state structure for iterating from 12-bit words to FAT12ClusterEntry values
pub struct IntoFAT16ClusterChainIter<'a> {
    /// The cluster chain entries to generate the iterator from.
    pub data: &'a [u16],
    /// index of the current position in the data.
    pub index: usize,
    /// The EOC marker for this FAT.
    pub eoc_marker: u16,
}

impl<'a> IntoIterator for FAT16ClusterChain<'a> {
    type Item = FAT16ClusterEntry;
    type IntoIter = IntoFAT16ClusterChainIter<'a>;

    /// Build an iterator for this cluster chain
    fn into_iter(self) -> IntoFAT16ClusterChainIter<'a> {
        IntoFAT16ClusterChainIter {
            data: self.raw_data,
            index: 0,
            eoc_marker: 0xFFFF,
        }
    }
}

impl<'a> FAT16ClusterChain<'a> {
    /// Build an iterator for this cluster chain
    /// The iteration starts at cluster number cluster
    pub fn into_iter_from_cluster(self, cluster: usize) -> IntoFAT16ClusterChainIter<'a> {
        IntoFAT16ClusterChainIter {
            data: self.raw_data,
            index: cluster,
            eoc_marker: 0xFFFF,
        }
    }
}

/// Second-level iterator, from 12-byte words to FAT12ClusterEntries
/// It's redundant shit, it really is, but it works
/// trait bounds, trait objects, all kinds of beautiful language features
/// but here we are
impl Iterator for IntoFAT16ClusterChainIter<'_> {
    type Item = FAT16ClusterEntry;

    fn next(&mut self) -> Option<Self::Item> {
        if (self.index < self.data.len())
            && (self.data[self.index] != self.eoc_marker)
            // FreeCluster is also considered EOC marker in cluster chains
            && (self.data[self.index] != 0x0000)
        {
            let item = self.data[self.index];
            self.index += 1;
            Some(parse_fat16_value(item))
        } else {
            None
        }
    }
}

/// The actual File Allocation Table in the FAT filesystem
/// This project only supports older filesystems
#[derive(Debug, PartialEq)]
pub enum FAT<'a> {
    /// FAT12 File Allocation Table
    FAT12(FATFAT12<'a>),
    /// FAT16 File Allocation Table
    FAT16(FATFAT16<'a>),
    /// Unknown FAT filesystem type
    Unknown,
}

/// Display a File Allocation Table
impl Display for FAT<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            FAT::FAT12(fat) => write!(f, "{}", fat),
            FAT::FAT16(fat) => write!(f, "{}", fat),
            _ => {
                panic!("Unknown FAT type");
            }
        }
    }
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

/// Parse two bytes into one 16-bit word, little-endian format
/// So 0x01 0x00 -> 0x0001
pub fn little_endian_16_bit_parser(i: &[u8]) -> IResult<&[u8], u16> {
    let result = le_u16(i)?;

    Ok(result)
}

mod tests {
    // For some reason this allow(unused_imports) is required in tests or inner modules
    // with the Rust 1.59.0 release
    #[allow(unused_imports)]
    use crate::cluster::{
        FAT12ClusterChain, FAT12ClusterEntry, FAT16ClusterChain, FAT16ClusterEntry,
    };
    #[allow(unused_imports)]
    use crate::cluster::{FATFAT12, FATFAT16};
    #[allow(unused_imports)]
    use crate::fat::{
        BIOSParameterBlock, DOS3FATBootSector, FATBootSector, FATBootSectorSignature,
        FATBootSectorStart, LogicalSectorsPerCluster,
    };
    #[allow(unused_imports)]
    use std::collections::HashMap;

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

    /// Test parsing 16-bit values
    #[test]
    fn little_endian_16_bit_parser_works() {
        // [0x12, 0x34, 0x56] should parse as [0x0412, 0x0563]
        let data: [u8; 2] = [0x12, 0x34];

        let little_endian_16_bit_parser_result = super::little_endian_16_bit_parser(&data);

        match little_endian_16_bit_parser_result {
            Ok((_, result)) => {
                assert_eq!(result, 0x3412);
            }
            Err(_) => panic!("Parser failed"),
        }
    }

    /// Test first-level iterating through a cluster
    #[test]
    fn first_level_cluster_iterator_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005]
        let data: [u8; 9] = [0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter().collect();
        assert_eq!(result[0], 0x002);
        assert_eq!(result[1], 0x003);
        assert_eq!(result[2], 0x004);
        assert_eq!(result[3], 0x005);
    }

    /// Test first-level iterator with a cluster index
    #[test]
    fn first_level_cluster_into_iter_from_cluster_zero_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005, 0x006, 0x007]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(0).collect();

        assert_eq!(result[0], 0x002);
        assert_eq!(result[1], 0x003);
        assert_eq!(result[2], 0x004);
        assert_eq!(result[3], 0x005);
        assert_eq!(result[4], 0x006);
        assert_eq!(result[5], 0x007);
    }

    /// Test first-level iterator with cluster index one
    #[test]
    fn first_level_cluster_into_iter_from_cluster_one_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005, 0x006, 0x007]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(1).collect();

        assert_eq!(result[0], 0x003);
        assert_eq!(result[1], 0x004);
        assert_eq!(result[2], 0x005);
        assert_eq!(result[3], 0x006);
        assert_eq!(result[4], 0x007);
    }

    /// Test first-level iterator last item
    #[test]
    fn first_level_cluster_into_iter_from_cluster_last_item() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005, 0x006, 0x007]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(5).collect();
        assert_eq!(result[0], 0x007);
    }

    /// Test first-level iterator with cluster index out of range even
    #[test]
    fn first_level_cluster_into_iter_from_cluster_out_of_range_even_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005, 0x006, 0x007]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(6).collect();
        assert_eq!(result.len(), 0);
    }

    /// Test first-level iterator out of range
    #[test]
    fn first_level_cluster_into_iter_from_cluster_out_of_range_odd_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005, 0x006, 0x007]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0x06, 0x70, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(7).collect();
        assert_eq!(result.len(), 0);
    }

    /// Test iterating through 12-bit words as a cluster chain
    #[test]
    fn second_level_cluster_iterator_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0x02, 0x30, 0x00, 0x04, 0x50, 0x00, 0xFF, 0x0F, 0x00,
        ];

        let cluster_chain = FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter().collect();

        let cluster_chain = FAT12ClusterChain {
            eoc_marker: 0xFFF,
            raw_data: &result,
        };

        let result2: Vec<FAT12ClusterEntry> = cluster_chain.into_iter().collect();

        assert_eq!(result2.len(), 4);
        assert_eq!(result2[0], FAT12ClusterEntry::DataCluster(0x002));
        assert_eq!(result2[1], FAT12ClusterEntry::DataCluster(0x003));
        assert_eq!(result2[2], FAT12ClusterEntry::DataCluster(0x004));
        assert_eq!(result2[3], FAT12ClusterEntry::DataCluster(0x005));
    }

    /// Test parsing 12-bit values
    #[test]
    fn fat_fat12_parser_works() {
        let oem_name = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let data: [u8; 6] = [0xF8, 0xFF, 0xFF, 0x03, 0x40, 0x00];

        let mut new_data: [u8; 32768] = [0; 32768];

        for i in 0..6 {
            new_data[i] = data[i];
        }

        let fat_boot_sector = FATBootSector {
            fat_boot_sector_start: FATBootSectorStart::DOS3(DOS3FATBootSector {
                jump_instruction: 0x00,
                jump_location: 0x00,
                nop_instruction: 0x00,
                oem_name: &oem_name,
            }),
            bios_parameter_block: BIOSParameterBlock {
                bytes_per_logical_sector: 512,
                logical_sectors_per_cluster: LogicalSectorsPerCluster::Four,
                count_of_reserved_logical_sectors: 4,
                number_of_fats: 2,
                maximum_number_of_root_directory_entries: 512,
                total_logical_sectors: 32000,
                media_descriptor: 0xF8,
                logical_sectors_per_fat: 32,
            },
            boot_code: None,
            signature: FATBootSectorSignature::IBMPC([0x55, 0xAA]),
        };

        let fat_fat12_parser_result = super::fat_fat12_parser(&fat_boot_sector)(&new_data);

        match fat_fat12_parser_result {
            Ok((_, result)) => {
                assert_eq!(result.fat_clusters[0].len(), 2);
                assert_eq!(
                    result.fat_clusters[0][0],
                    FAT12ClusterEntry::DataCluster(0x03)
                );
                assert_eq!(
                    result.fat_clusters[0][1],
                    FAT12ClusterEntry::DataCluster(0x04)
                );
            }
            Err(_) => panic!("Parser failed"),
        }
    }

    /// Test parsing 16-bit values
    #[test]
    fn fat_fat16_parser_works() {
        let oem_name = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let data: [u8; 16] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x04, 0x00, 0x05, 0x00, 0x06, 0x00, 0x07, 0x00,
            0x08, 0x00,
        ];

        let mut new_data: [u8; 32768] = [0; 32768];

        for i in 0..15 {
            new_data[i] = data[i];
        }

        let fat_boot_sector = FATBootSector {
            fat_boot_sector_start: FATBootSectorStart::DOS3(DOS3FATBootSector {
                jump_instruction: 0x00,
                jump_location: 0x00,
                nop_instruction: 0x00,
                oem_name: &oem_name,
            }),
            bios_parameter_block: BIOSParameterBlock {
                bytes_per_logical_sector: 512,
                logical_sectors_per_cluster: LogicalSectorsPerCluster::Four,
                count_of_reserved_logical_sectors: 4,
                number_of_fats: 2,
                maximum_number_of_root_directory_entries: 512,
                total_logical_sectors: 32000,
                media_descriptor: 0xF8,
                logical_sectors_per_fat: 32,
            },
            boot_code: None,
            signature: FATBootSectorSignature::IBMPC([0x55, 0xAA]),
        };

        let fat_fat16_parser_result = super::fat_fat16_parser(&fat_boot_sector)(&new_data);

        match fat_fat16_parser_result {
            Ok((_, result)) => {
                assert_eq!(result.fat_clusters[0].len(), 5);
                assert_eq!(
                    result.fat_clusters[0][0],
                    FAT16ClusterEntry::DataCluster(0x04)
                );
                assert_eq!(
                    result.fat_clusters[0][1],
                    FAT16ClusterEntry::DataCluster(0x05)
                );
                assert_eq!(
                    result.fat_clusters[0][2],
                    FAT16ClusterEntry::DataCluster(0x06)
                );
                assert_eq!(
                    result.fat_clusters[0][3],
                    FAT16ClusterEntry::DataCluster(0x07)
                );
                assert_eq!(
                    result.fat_clusters[0][4],
                    FAT16ClusterEntry::DataCluster(0x08)
                );
            }
            Err(_) => panic!("Parser failed"),
        }
    }

    /// Test first-level iterating through a 16-bit cluster
    #[test]
    fn first_level_16_bit_cluster_iterator_works() {
        // [0x01, 0x00, 0x02, 0x00, 0x03, 0x00] should parse as
        // [0x001, 0x002, 0x003]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x04, 0x00,
        ];

        let cluster_chain = FATFAT16 {
            fat_id: 0x00,
            eoc_marker: 0xFFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter().collect();
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], 0x002);
        assert_eq!(result[1], 0x003);
        assert_eq!(result[2], 0x004);
    }

    /// Test first-level iterating through a 16-bit cluster, starting at cluster zero
    #[test]
    fn first_level_16_bit_cluster_iterator_from_cluster_zero_works() {
        // [0x01, 0x00, 0x02, 0x00, 0x03, 0x00] should parse as
        // [0x001, 0x002, 0x003]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x04, 0x00,
        ];

        let cluster_chain = FATFAT16 {
            fat_id: 0x00,
            eoc_marker: 0xFFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(0).collect();
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], 0x002);
        assert_eq!(result[1], 0x003);
        assert_eq!(result[2], 0x004);
    }

    /// Test first-level iterating through a 16-bit cluster, starting at cluster one
    #[test]
    fn first_level_16_bit_cluster_iterator_from_cluster_one_works() {
        // [0x01, 0x00, 0x02, 0x00, 0x03, 0x00] should parse as
        // [0x001, 0x002, 0x003]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x04, 0x00,
        ];

        let cluster_chain = FATFAT16 {
            fat_id: 0x00,
            eoc_marker: 0xFFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(1).collect();
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], 0x003);
        assert_eq!(result[1], 0x004);
    }

    /// Test first-level iterating through a 16-bit cluster, starting at last item
    #[test]
    fn first_level_16_bit_cluster_iterator_from_cluster_last_item_works() {
        // [0x01, 0x00, 0x02, 0x00, 0x03, 0x00] should parse as
        // [0x001, 0x002, 0x003]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x04, 0x00,
        ];

        let cluster_chain = FATFAT16 {
            fat_id: 0x00,
            eoc_marker: 0xFFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter_from_cluster(2).collect();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], 0x004);
    }

    /// Test iterating through 16-bit words as a cluster chain
    #[test]
    fn second_level_16_bit_cluster_iterator_works() {
        // [0x02, 0x30, 0x00, 0x04, 0x50, 0x00] should parse as
        // [0x002, 0x003, 0x004, 0x005]
        let data: [u8; 12] = [
            0xF8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x04, 0x00,
        ];

        let cluster_chain = FATFAT16 {
            fat_id: 0x00,
            eoc_marker: 0xFFFF,
            fat_clusters: Vec::new(),
            fat_cluster_index: HashMap::new(),
            raw_data: &data,
        };

        let result: Vec<u16> = cluster_chain.into_iter().collect();

        let cluster_chain = FAT16ClusterChain {
            eoc_marker: 0xFFFF,
            raw_data: &result,
        };

        let result2: Vec<FAT16ClusterEntry> = cluster_chain.into_iter().collect();

        assert_eq!(result2.len(), 3);
        assert_eq!(result2[0], FAT16ClusterEntry::DataCluster(0x0002));
        assert_eq!(result2[1], FAT16ClusterEntry::DataCluster(0x0003));
        assert_eq!(result2[2], FAT16ClusterEntry::DataCluster(0x0004));
    }
}
