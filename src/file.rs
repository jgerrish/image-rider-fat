#![warn(missing_docs)]
#![warn(unsafe_code)]
//! File parsing helpers and functions
use log::error;

use crate::cluster::{parse_fat12_value, FAT12ClusterEntry, FAT};
use crate::fat::FATDisk;

/// Get the file data for a file.
/// This function is only valid for FAT12.
/// It uses the data region as cluster data.
///
/// # Arguments
///
/// - `disk` - A FATDisk structure that contains the disk or ROM image
/// - `filename` - The name of the file to get from the image.
///
/// # Returns
///
/// A u8 Vec containing the data in the file
///
pub fn get_file_data(disk: FATDisk, filename: &str) -> Vec<u8> {
    let mut data = Vec::new();

    let fat = match disk.fat {
        FAT::FAT12(f) => f,
        FAT::FAT16(_f) => {
            // This is going to require refactors
            error!("FAT16 not fully implemented yet");
            panic!("FAT16 not fully implemented yet");
        }
        // Don't remove this unless this code has been updated to deal
        // with > 32-bit file-sizes.
        // I don't know if this is a good pattern or not.
        // Having a dummy enum variant and pattern matching on the
        // wildcard seems useful to build versioning and fences into
        // the code.
        // But there are probably downsides.  Who knows, probably a
        // good style guide item.
        _ => {
            error!("Must be a FAT12 or FAT16 filesystem to get file data");
            panic!("Must be a FAT12 or FAT16 filesystem to get file data");
        }
    };

    let file = disk
        .directory_table
        .directory_by_filename
        .get(filename)
        .unwrap();

    // Given the above sanity checks, bytes_per_cluster should be
    // limited to less than 32 bits (21 bits).
    let bytes_per_cluster: u32 = disk
        .fat_boot_sector
        .bios_parameter_block
        .bytes_per_logical_sector as u32
        * disk
            .fat_boot_sector
            .bios_parameter_block
            .logical_sectors_per_cluster as u32;

    // This adjustment by two seems weird, but the cluster entry
    // values are correct.
    // For FAT32, the root directory lives in the data region, but not so
    // for FAT12 or FAT16.
    // From the fatgen103 document:
    // "The start of the data region, the first sector of cluster 2"
    // Unless the root directory table or FAT is considered part of
    // the data region.
    let start_cluster_index = file.start_of_file - 2;

    // We need to piece together the clusters
    let words_iter = fat.into_iter_from_cluster(start_cluster_index as usize);
    let indexes = words_iter.map_while(|entry| match parse_fat12_value(entry) {
        FAT12ClusterEntry::EndOfChainMarker(_) => None,
        _ => Some(entry),
    });

    // Just a sanity check to assist with casts
    // We'll set the maximum image size to u32::MAX
    if u64::from(start_cluster_index) > u32::MAX.into() {
        error!("start cluster index exceeds sanity check size");
        panic!("start cluster index exceeds sanity check size");
    }

    // casting from an integer to a float will "produce the closest possible float"
    // The Rust Language Reference - Operator Expressions
    let clusters_in_file: u32 = (file.file_size as f32 / bytes_per_cluster as f32).ceil() as u32;

    // Deal with the start of the file, including the cases where the
    // file is a multiple of the bytes per cluster, and the case where
    // it isn't.
    if clusters_in_file == 1 {
        if (file.file_size % bytes_per_cluster) == 0 {
            data.extend_from_slice(disk.data_region_as_clusters[start_cluster_index as usize]);
        } else {
            let cluster_data = disk.data_region_as_clusters[start_cluster_index as usize];
            data.extend_from_slice(&cluster_data[0..(file.file_size % bytes_per_cluster) as usize]);
        }
    } else {
        data.extend_from_slice(disk.data_region_as_clusters[start_cluster_index as usize]);
    }

    if clusters_in_file >= 2 {
        for (i, cluster) in indexes.enumerate() {
            if (i + 3) > clusters_in_file.try_into().unwrap() {
                if (file.file_size % bytes_per_cluster) == 0 {
                    data.extend_from_slice(disk.data_region_as_clusters[(cluster - 2) as usize]);
                } else {
                    let cluster_data = disk.data_region_as_clusters[(cluster - 2) as usize];
                    data.extend_from_slice(
                        &cluster_data[0..(file.file_size % bytes_per_cluster) as usize],
                    );
                }
                break;
            } else {
                data.extend_from_slice(disk.data_region_as_clusters[(cluster - 2) as usize]);
            }
        }
    }

    data
}

#[cfg(test)]
mod tests {
    use crate::cluster::{FAT12ClusterEntry, FAT, FATFAT12};
    use crate::directory_table::{FATDirectory, FATDirectoryEntry, FileType};
    use crate::fat::{
        BIOSParameterBlock, DOS3FATBootSector, FATBootSector, FATBootSectorSignature,
        FATBootSectorStart, FATDisk, LogicalSectorsPerCluster,
    };
    use log::error;

    #[allow(unused_imports)]
    use std::collections::HashMap;

    use super::get_file_data;

    /// Build a generic BIOS Parameter Block
    fn build_bios_parameter_block() -> BIOSParameterBlock {
        BIOSParameterBlock {
            bytes_per_logical_sector: 512,
            logical_sectors_per_cluster: LogicalSectorsPerCluster::Two,
            count_of_reserved_logical_sectors: 1,
            number_of_fats: 2,
            maximum_number_of_root_directory_entries: 112,
            total_logical_sectors: 720,
            media_descriptor: 0xF8,
            logical_sectors_per_fat: 2,
        }
    }

    fn build_dos3_boot_sector<'underlying_raw_data>() -> DOS3FATBootSector<'underlying_raw_data> {
        DOS3FATBootSector {
            jump_instruction: 0xEB,
            jump_location: 0x3C,
            nop_instruction: 0x90,
            oem_name: &[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        }
    }

    /// Build a FATFAT12 cluster chain
    /// NOTE: This is limited to 2 clusters for testing purposes
    fn build_limited_fat_fat_12<'a>(num_clusters: u16) -> FATFAT12<'a> {
        if num_clusters > 2 {
            error!("Testing doesn't support more than two clusters");
            panic!("Testing doesn't support more than two clusters");
        }

        let mut cluster1 = Vec::new();
        for i in 0..num_clusters {
            cluster1.push(FAT12ClusterEntry::DataCluster(i + 3));
        }
        // cluster1.push(FAT12ClusterEntry::EndOfChainMarker(0xFFF));

        let mut fat_clusters = Vec::new();
        fat_clusters.push(cluster1);

        FATFAT12 {
            fat_id: 0x00,
            eoc_marker: 0xFFF,
            fat_clusters,
            fat_cluster_index: HashMap::new(),
            raw_data: match num_clusters {
                1 => &[0xF8, 0xFF, 0xFF, 0x03, 0x00, 0x00],
                2 => &[0xF8, 0xFF, 0xFF, 0x03, 0x40, 0x00],
                _ => &[0xF8, 0xFF, 0xFF, 0x00, 0x00, 0x00],
            },
        }
    }

    /// Build a FAT disk with a file with data
    fn build_disk_with_file<'underlying_raw_data>(
        filename: &str,
        filedata: &'underlying_raw_data [u8],
        filesize: u32,
    ) -> FATDisk<'underlying_raw_data> {
        let dos3_boot_sector = build_dos3_boot_sector();
        let bios_parameter_block = build_bios_parameter_block();
        let fat_boot_sector_start = FATBootSectorStart::DOS3(dos3_boot_sector);

        let fat_boot_sector = FATBootSector {
            fat_boot_sector_start,
            bios_parameter_block,
            boot_code: None,
            signature: FATBootSectorSignature::IBMPC([0x55, 0xAA]),
        };

        let cluster_size_in_bytes: u32 = bios_parameter_block.logical_sectors_per_cluster as u32
            * bios_parameter_block.bytes_per_logical_sector as u32;

        let num_clusters = (filedata.len() as f32 / cluster_size_in_bytes as f32).ceil() as usize;

        let fat = FAT::FAT12(build_limited_fat_fat_12(
            (num_clusters - 1).try_into().unwrap(),
        ));
        let fat2 = FAT::FAT12(build_limited_fat_fat_12(
            (num_clusters - 1).try_into().unwrap(),
        ));

        let mut cluster_data = Vec::new();

        if (num_clusters == 0) && (filedata.len() > 0) {
            let data = &filedata[0..filedata.len()];
            cluster_data.push(data);
        } else {
            for i in 0..num_clusters {
                let start: usize = i as usize * cluster_size_in_bytes as usize;
                let end: usize = start + cluster_size_in_bytes as usize;

                let data = if end > filedata.len() {
                    // file is not a multiple of cluster_size_in_bytes
                    &filedata[start..filedata.len()]
                } else {
                    // file is a multiple of cluster_size_in_bytes
                    &filedata[start..end]
                };
                cluster_data.push(data);
            }
        }

        let directory_entry = FATDirectoryEntry {
            full_filename: filename.to_string(),
            filename: filename.to_string(),
            file_extension: String::from(""),
            file_attributes: 0,
            user_attributes: 0,
            deleted_file_first_character: 0,
            create_time: None,
            create_date: None,
            last_access_date: None,
            extended_attributes: 0,
            last_modified_time: None,
            last_modified_date: None,
            start_of_file: 2,
            file_size: filesize,
        };
        let mut directory_entries = Vec::new();
        let new_entry = directory_entry.clone();
        directory_entries.push(FileType::Normal(directory_entry));

        let mut directory_by_filename = HashMap::<String, FATDirectoryEntry>::new();
        directory_by_filename.insert(new_entry.full_filename.clone(), new_entry);
        let directory_table = FATDirectory {
            directory_by_filename,
            directory_entries,
        };
        FATDisk {
            fat_boot_sector,
            fat,
            backup_fat: Some(fat2),
            directory_table,
            data_region: filedata,
            data_region_as_clusters: cluster_data,
        }
    }

    /// Test that getting data from a cluster-size file works.
    #[test]
    fn get_file_data_cluster_size_works() {
        let mut data = [0; 1024];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[1023] = 1;
        data[1022] = 2;
        data[1021] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 1024);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }

    /// Test that getting data from a less-than cluster-size file
    /// works.
    #[test]
    fn get_file_data_less_than_cluster_size_works() {
        let mut data = [0; 1020];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[1019] = 1;
        data[1018] = 2;
        data[1017] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 1020);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }

    /// Test that getting data from a file with filesize == two
    /// clusters works.
    #[test]
    fn get_file_data_two_cluster_sizes_works() {
        let mut data = [0; 2048];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[2047] = 1;
        data[2046] = 2;
        data[2045] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 2048);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }

    /// Test that getting data from a file with filesize == two
    /// clusters works.
    #[test]
    fn get_file_data_two_cluster_sizes_non_bytes_per_cluster_multiple_works() {
        let mut data = [0; 2040];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[2039] = 1;
        data[2038] = 2;
        data[2037] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 2040);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }

    /// Test that getting data from a file with filesize == three
    /// clusters works.
    #[test]
    fn get_file_data_three_cluster_sizes_works() {
        let mut data = [0; 3072];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[3071] = 1;
        data[3070] = 2;
        data[3069] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 3072);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }

    /// Test that getting data from a file with filesize == three
    /// clusters works.
    #[test]
    fn get_file_data_three_cluster_sizes_non_bytes_per_cluster_multiple_works() {
        let mut data = [0; 3068];
        data[0] = 1;
        data[1] = 2;
        data[2] = 3;
        data[3067] = 1;
        data[3066] = 2;
        data[3065] = 3;

        let disk = build_disk_with_file(&String::from("TEST"), &data, 3068);

        let res = get_file_data(disk, &String::from("TEST"));

        assert_eq!(data.to_vec(), res);
    }
}
