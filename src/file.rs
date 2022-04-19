use log::error;

use crate::cluster::{parse_fat12_value, FAT12ClusterEntry, FAT};
use crate::fat::FATDisk;

/// Get the file data for a file
pub fn get_file_data(disk: FATDisk, filename: &String) -> Vec<u8> {
    let file = disk
        .directory_table
        .directory_by_filename
        .get(filename)
        .unwrap();

    let fat = match disk.fat {
        FAT::FAT12(f) => f,
        FAT::FAT16(_f) => {
            // This is going to require refactors
            error!("FAT16 not fully implemented yet");
            panic!("FAT16 not fully implemented yet");
        }
    };

    let sector_size = disk
        .fat_boot_sector
        .bios_parameter_block
        .bytes_per_logical_sector as u32
        * disk
            .fat_boot_sector
            .bios_parameter_block
            .logical_sectors_per_cluster as u32;

    // This adjustment by two seems weird, but the cluster entry values are correct
    // Unless the root directory table or FAT is considered part of the data region
    let start: usize = ((file.start_of_file as u32 - 2) * sector_size as u32) as usize;
    let end: usize = start + file.file_size as usize;
    let start_cluster_index = file.start_of_file - 2;
    let mut data = Vec::new();
    let mut written: u32 = 0;

    if file.file_size > sector_size as u32 {
        data.extend_from_slice(
            &disk.data_region[(start as usize)..((sector_size as usize) + start)],
        );
        written += sector_size as u32;
        // We need to piece together the clusters
        let words_iter = fat.into_iter_from_cluster(start_cluster_index as usize);

        // This should probably be moved into the cluster code
        let indexes = words_iter.map_while(|entry| match parse_fat12_value(entry) {
            FAT12ClusterEntry::EndOfChainMarker(_) => None,
            _ => Some(entry),
        });

        for cluster in indexes {
            // The amount of data to read
            let to_read = if (written + sector_size as u32) > file.file_size {
                (file.file_size - written) as usize
            } else {
                sector_size as usize
            };

            let slice_start = ((cluster as u32 - 2) * sector_size as u32) as usize;
            let slice_end = (slice_start + to_read) as usize;
            data.extend_from_slice(&disk.data_region[slice_start..slice_end]);
            written += slice_end as u32 - slice_start as u32;
        }
        data
    } else {
        Vec::from(&disk.data_region[start..end])
    }
}
