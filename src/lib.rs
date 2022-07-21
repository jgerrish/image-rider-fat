#![warn(missing_docs)]
#![warn(unsafe_code)]
//! MS-DOS FAT disk image parser
use log::error;

/// MS-DOS FAT disk images
pub mod fat;

/// File Allocation Table Cluster functions and data structures
pub mod cluster;

/// SanityCheck trait
pub mod sanity_check;

/// FAT Directory Table parser
pub mod directory_table;

/// File-handling functions
/// This module combines the directory table with the FAT cluster
/// to piece together files
pub mod file;

/// Initialize the module.
/// This should be called before any parsing is performed.
/// Panics on failure or if there are any incompatibilities.
pub fn init() {
    // If we're on a system with a usize < 32 bits, fail
    // From Design of the FAT file system, WikiPedia
    // FAT12 maximum size is 133,824,512 bytes
    // FAT16 maximum size is 2,147,090,432 bytes
    if usize::BITS < 32 {
        error!(
            "Architecture usize {} is too small for this library",
            usize::BITS
        );
        panic!(
            "Architecture usize {} is too small for this library",
            usize::BITS
        );
    }
}
