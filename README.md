# image-rider-fat
![build](https://github.com/jgerrish/image-rider-fat/actions/workflows/rust.yml/badge.svg)

Rust nom parser to read FAT file systems


This is a library of parsers built using the nom parsing framework to
parse DOS FAT disk images.

# Supported Formats

The following formats are currently detected.  Parsing is not fully
implemented for any of them yet.

FAT12: Basic File Allocation Table parsing
FAT16: Basic skeleton but it's not working


# Usage

You can run the example application with the following command:

RUST_LOG=debug cargo run --example parser -- --input FILENAME

