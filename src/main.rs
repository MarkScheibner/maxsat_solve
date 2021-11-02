use std::{fs, io::{self, Read}};
use pico_args::Arguments;
use rand::{ rngs::StdRng, SeedableRng };
mod parser;
mod graph;
mod fasttw;

fn main() -> anyhow::Result<()>{
	let mut rng = StdRng::seed_from_u64(crate::fasttw::SEED);

	// get file name for WCNF file
	let mut args = Arguments::from_env();
	let file_name: Option<String> = args.value_from_str("--file").or_else(|_| args.value_from_str("-f")).ok();
	// read contents from file or stdin depending on command line arguments
	let mut contents = String::new();
	let mut reader: Box<dyn std::io::Read> = match file_name {
		Some(file_name) => Box::new(fs::File::open(file_name)?),
		None => Box::new(io::stdin())
	};
	// decompress if needed
	if args.contains("-c") || args.contains("--compressed") {
		reader = Box::new(flate2::read::GzDecoder::new(reader));
	}
	reader.read_to_string(&mut contents)?;

	// parse formula
	let mut formula = parser::Formula::from(contents);
	// preprocess formula
	let size_before = formula.get_parameters().n_clauses;
	let (_renaming, _removed) = formula.unit_propagation();
	let size_reduction = size_before - formula.get_parameters().n_clauses;
	// split formula
	let (sub_formulae, _renamings) = formula.sub_formulae();
	
	// create graphs from each sub-formula
	let primal = args.contains("-p") || args.contains("--primal");
	let dual = args.contains("-d") || args.contains("--dual");
	let _incidence = args.contains("-i") || args.contains("--incidence");
	let graphs: Vec<_> = sub_formulae.into_iter().map(|f| if primal {
		Box::new(graph::PrimalGraph::from(f)) as Box<dyn graph::Graph>
	} else if dual {
		Box::new(graph::DualGraph::from(f)) as Box<dyn graph::Graph>
	} else  {
		Box::new(graph::IncidenceGraph::from(f)) as Box<dyn graph::Graph>
	}).collect();
	
	// some useful values
	let nodes       = graphs.iter().fold(0, |c_nodes, g| c_nodes +  g.size());
	let edges       = graphs.iter().fold(0, |c_edges, g| c_edges + g.list_edges().len());
	let components  = graphs.len();
	let mut max_deg = 0;
	let mut min_deg = usize::MAX;
	let mut tw      = 0;
	for graph in &graphs {
		max_deg = (0..graph.size()).map(|i| graph.neighborhood(i).len()).fold(max_deg, |c_max, d| d.max(c_max));
		min_deg = (0..graph.size()).map(|i| graph.neighborhood(i).len()).fold(min_deg, |c_min, d| d.min(c_min));
	}

	if min_deg > 100 || nodes * 100 < edges {
		// don't even bother
		println!("{}, {}, {}, {}, {}, {}, {}", nodes, edges, components, max_deg, min_deg, size_reduction, -1);
		std::process::exit(1);
	}
	
	for graph in graphs {
		// see if we can compute a peo and tree-decomposition before the timer runs out
		// TODO optimize this.
		let mut decomposition_graph = fasttw::Graph::new(graph.size());
		graph.list_edges().iter().for_each(|(u, v)| decomposition_graph.add_edge(*u, *v));
		let peo = decomposition_graph.compute_peo(&mut rng);
		let td = decomposition_graph.peo_to_decomposition(&peo).unwrap();
		tw = td.iter().map(|(_,bag)| bag.len()).fold(tw, |c_tw, l_tw| l_tw.max(c_tw));

		// TODO do cool stuff with decomposition
	}

	println!("{}, {}, {}, {}, {}, {}, {}", nodes, edges, components, max_deg, min_deg, size_reduction, tw);
	Ok(())
}
