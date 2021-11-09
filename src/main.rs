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
	let (_assignment, _renaming) = formula.preprocess();
	let size_reduction = size_before - formula.get_parameters().n_clauses;
	// split formula
	let (sub_formulae, _renamings) = formula.sub_formulae();
	
	let primal = args.contains("-p") || args.contains("--primal");
	let dual   = args.contains("-d") || args.contains("--dual");
	
	// create graphs from each sub-formula
	let graphs: Vec<_> = sub_formulae.into_iter().map(|f| if primal {
		Box::new(graph::Primal::from(f)) as Box<dyn graph::Graph>
	} else if dual {
		Box::new(graph::Dual::from(f)) as Box<dyn graph::Graph>
	} else  {
		Box::new(graph::Incidence::from(f)) as Box<dyn graph::Graph>
	}).collect();
	
	// some useful values
	let nodes       = graphs.iter().map(|g| g.size()).collect::<Vec<_>>();
	let edges       = graphs.iter().map(|g| g.edge_count()).collect::<Vec<_>>();
	let num_nodes   = nodes.iter().sum::<usize>();
	let num_edges   = edges.iter().sum::<usize>();
	let components  = graphs.len();
	let mut tw      = 0;
	let degrees     = graphs.iter().map(|g| {
		let max_deg = (0..g.size()).map(|i| g.degree(i)).fold(0,          |c_max, d| d.max(c_max));
		let min_deg = (0..g.size()).map(|i| g.degree(i)).fold(usize::MAX, |c_min, d| d.min(c_min));
		(min_deg, max_deg)
	}).collect::<Vec<_>>();
	let g_max_deg   = degrees.iter().fold(0,          |c_max, &(_, max)| c_max.max(max));
	let g_min_deg   = degrees.iter().fold(usize::MAX, |c_min, &(min, _)| c_min.min(min));
	let max_min_deg = degrees.iter().map(|&(min, _)| min).max().unwrap_or(0);

	// see if we should even bother. mindeg and e/v are lower bounds for treewidth.
	if degrees.iter().any(|&(min, _)| min > 100) || nodes.iter().zip(&edges).any(|(v, e)| v * 100 < *e) {
		// don't even bother
		println!("{}, {}, {}, {}, {}, {}, {}, {}", num_nodes, num_edges, components, g_max_deg, g_min_deg, max_min_deg, size_reduction, -1);
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

	println!("{}, {}, {}, {}, {}, {}, {}, {}", num_nodes, num_edges, components, g_max_deg, g_min_deg, max_min_deg, size_reduction, tw);
	Ok(())
}
