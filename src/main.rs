use std::{fs, io::{self, Read}};
use pico_args::Arguments;
use rand::{ rngs::StdRng, SeedableRng };
use anyhow::bail;
mod parser;
mod graph;
mod fasttw;

/// Seed of the random number generator.
const SEED: u64 = 42;

fn main() -> anyhow::Result<()>{
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
	let mut formula = parser::Formula::new(contents);
	let size_before = formula.get_parameters().n_clauses;
	formula.unit_propagation();
	let size_reduction = size_before - formula.get_parameters().n_clauses;

	let primal = args.contains("-p") || args.contains("--primal");
	let dual = args.contains("-d") || args.contains("--dual");
	let incidence = args.contains("-i") || args.contains("--incidence");
	
	let graph: Box<dyn graph::Graph> = if primal {
		Box::new(graph::PrimalGraph::from(formula))
	} else if dual {
		Box::new(graph::DualGraph::from(formula))
	} else if incidence {
		Box::new(graph::IncidenceGraph::from(formula))
	} else {
		bail!("Please provide option -p, -d or -i");
	};

	// calculate some values of the graph
	let nodes = graph.size();
	let edges = graph.list_edges().len();
	let (max, min) = (0..nodes).map(|i| graph.neighborhood(i).len())
	                           .fold((0, graph.size()), |(max, min), s| (s.max(max), s.min(min)));
	
	println!("{}, {}, {}, {}, {}", nodes, edges, max, min, size_reduction);
	
	if min > 100 {
		// don't even bother
		std::process::exit(1);
	}

	// see if we can comput a peo before the timer runs out
	let mut rng = StdRng::seed_from_u64(SEED);
	// TODO optimize this.
	let mut decomposition_graph = fasttw::Graph::new(graph.size());
	graph.list_edges().iter().for_each(|(u, v)| decomposition_graph.add_edge(*u, *v));
	let _peo = decomposition_graph.compute_peo(&mut rng);

	// TODO do cool stuff with graph

	Ok(())
}
