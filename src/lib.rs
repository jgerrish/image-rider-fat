// 1/// MS-DOS FAT disk image parser
#[warn(missing_docs)]
#[warn(unsafe_code)]

/// MS-DOS FAT disk images
pub mod fat;

/// SanityCheck trait
pub mod sanity_check;

/// FAT Directory Table parser
pub mod directory_table;
