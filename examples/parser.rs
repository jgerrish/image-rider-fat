/// Parse an image file
/// Usage: cargo run --example parser --input FILENAME
///
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::exit;

use clap::Parser;
use config::Config;
use env_logger;
use log::{error, info};

use image_rider_fat::fat::fat_disk_parser;
use image_rider_fat::file::get_file_data;

/// Command line arguments to parse an image file
#[derive(Parser, Debug)]
#[clap(about, version, author)]
struct Args {
    /// Filename to parse
    #[clap(short, long)]
    input: String,

    /// Explicitly specify a FAT version or operating system
    /// Currently allowed types are:
    /// AtariST, DOS2, DOS3
    /// This forces some internal parse paths even if auto-detection fails
    #[clap(long)]
    filesystem_type: Option<String>,

    /// Explicitly specify bits per FAT entry (e.g. FAT12, FAT16, FAT32) as number
    #[clap(short = 'b', long)]
    filesystem_bits: Option<u8>,

    /// Explicitly specify a root directory location
    /// The location is an absolute address
    #[clap(short, long)]
    root_directory_location: Option<u32>,

    /// Specify a file to operate on
    #[clap(short, long)]
    filename: Option<String>,

    /// Specify an output filename to write to
    #[clap(short, long)]
    output: Option<String>,

    /// Verbose mode will print information while parsing the image file
    #[clap(short, long)]
    verbose: bool,
}

/// Open up a file and read in the data
/// Returns all the data as a u8 vector
pub fn open_file(filename: &str) -> Vec<u8> {
    let path = Path::new(&filename);

    let mut file = match File::open(&path) {
        Err(why) => panic!("Couldn't open {}: {}", path.display(), why),
        Ok(file) => file,
    };

    let mut data = Vec::<u8>::new();

    let result = file.read_to_end(&mut data);

    match result {
        Err(why) => {
            error!("Error reading file: {}", why);
            panic!("Error reading file: {}", why);
        }
        Ok(result) => info!("Read {}: {} bytes", path.display(), result),
    };

    data
}

/// Parse an image file
fn main() {
    // Load config
    let mut _debug = true;

    // Initialize logger
    if let Err(e) = env_logger::try_init() {
        panic!("couldn't initialize logger: {:?}", e);
    }

    let settings_result = load_settings("config/image-rider-fat.toml");
    match settings_result {
        Ok(settings) => {
            info!("merged in config");
            if let Ok(b) = settings.get_bool("debug") {
                _debug = b;
            }
        }
        Err(s) => {
            error!("error loading config: {:?}", s)
        }
    };

    // Parse command line arguments
    let args = Args::parse();

    let data = open_file(&args.input);

    // Parse the image data
    let result = fat_disk_parser(
        &args.filesystem_type,
        args.filesystem_bits,
        &args.root_directory_location,
    )(&data);

    let (_, image) = match result {
        Err(e) => {
            error!("{}", e);
            exit(1);
        }
        Ok(res) => {
            if args.verbose {
                println!("Disk: {}", res.1);
            }
            res
        }
    };

    if args.filename.is_some() {
        let image_data = get_file_data(image, &args.filename.as_ref().unwrap());

        let filename = PathBuf::from(&args.output.unwrap());
        let file_result = File::create(filename);
        match file_result {
            Ok(mut file) => {
                let _res = file.write_all(&image_data);
            }
            Err(e) => error!("Error opening file: {}", e),
        }
    }

    exit(0);
}

/// load settings from a config file
/// returns the config settings as a Config on success, or a ConfigError on failure
fn load_settings<'a>(config_name: &str) -> Result<Config, config::ConfigError> {
    Config::builder()
        // Add in config file
        .add_source(config::File::with_name(config_name))
        // Add in settings from the environment (with a prefix of APP)
        // Eg.. `APP_DEBUG=1 ./target/command_bar_widget would set the `debug` key
        .add_source(config::Environment::with_prefix("APP"))
        .build()
}
