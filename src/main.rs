use std::{fs, io::{self, Read}};
use pico_args::Arguments;
mod parser;
mod graph;




fn main() {
	// get file name for WCNF file
	let mut args = Arguments::from_env();
	let file_name: Option<String> = args.value_from_str("--file").or_else(|_| args.value_from_str("-f")).ok();
	
	// read contents from file or stdin depending on command line arguments
	let mut contents = String::new();
	let mut reader: Box<dyn std::io::Read> = match file_name {
		Some(file_name) => Box::new(fs::File::open(file_name).expect("Error reading file")),
		None => Box::new(io::stdin())
	};

	// decompress if needed
	if args.contains("-c") || args.contains("--compressed") {
		reader = Box::new(flate2::read::GzDecoder::new(reader));
	}

	reader.read_to_string(&mut contents).expect("Error reading file");

	// parse formula
	let formula = parser::Formula::new(contents);

	// TODO do cool stuff with formula

}
