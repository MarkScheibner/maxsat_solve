use std::io::Write;
use std::{fs, io::{self, Read}};
// use fasttw::print;
use pico_args::Arguments;
use rand::{ rngs::StdRng, SeedableRng };
use solver::Solve;

mod parser;
mod graph;
mod fasttw;
mod solver;

use crate::graph::Graph;


fn main() -> anyhow::Result<()>{
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

	// parse, preprocess and split formula
	let mut formula                = parser::Formula::from(contents);
	let size_before                = formula.n_clauses;
	let (_assignment, _renaming)   = formula.preprocess().unwrap();
	let _size_reduction            = size_before - formula.n_clauses;
	let (sub_formulae, _renamings) = formula.split();
	
	let use_primal = args.contains("-p") || args.contains("--primal");
	let use_dual   = args.contains("-d") || args.contains("--dual");
	
	// get variable assignment for each subformula
	let _sub_assignments = if use_primal {
		solve_formulas::<graph::Primal>(sub_formulae)
	} else if use_dual {
		solve_formulas::<graph::Dual>(sub_formulae)
	} else {
		solve_formulas::<graph::Incidence>(sub_formulae)
	};

	// TODO unpack sub_assignments into preprocessed asignment
	Ok(())
}

fn solve_formulas<T>(sub_formulas: Vec<parser::Formula>) -> Option<Vec<Vec<bool>>> 
where T: Solve + Graph + From<parser::Formula> + std::fmt::Debug {
	let mut rng = StdRng::seed_from_u64(crate::fasttw::SEED);
	let mut assignments = Vec::with_capacity(sub_formulas.len());

	for (i, formula) in sub_formulas.into_iter().enumerate() {
		let graph = T::from(formula);
		let mut decomposition_graph = fasttw::Graph::new(graph.size());
		graph.list_edges().iter().for_each(|(u, v)| decomposition_graph.add_edge(*u, *v));
		let peo = decomposition_graph.compute_peo(&mut rng);
		let td  = decomposition_graph.peo_to_decomposition(&peo)?;
		let k   = td.iter().map(|(_, bag)| bag.len()).max().unwrap_or(0);
		let mut file = fs::File::create(format!("../graph_{}.gr", i)).unwrap();
		write!(file, "{}", graph.print()).unwrap();
		let mut file = fs::File::create(format!("../graph_{}.td", i)).unwrap();
		write!(file, "{}", fasttw::print(&td, k, graph.size())).unwrap();
		let local_solution = graph.solve(td, k)?;
		assignments.push(local_solution.0);
	}

	println!("Found an assignment for all parts");
	Some(assignments)
}

fn print_values(graphs: &Vec<impl graph::Graph>, size_reduction: usize) {
	// some useful values
	let nodes       = graphs.iter().map(|g| g.size()).collect::<Vec<_>>();
	let edges       = graphs.iter().map(|g| g.edge_count()).collect::<Vec<_>>();
	let num_nodes   = nodes.iter().sum::<usize>();
	let num_edges   = edges.iter().sum::<usize>();
	let components  = graphs.len();
	let degrees     = graphs.iter().map(|g| {
		let max_deg = (0..g.size()).map(|i| g.degree(i)).fold(0,          |c_max, d| d.max(c_max));
		let min_deg = (0..g.size()).map(|i| g.degree(i)).fold(usize::MAX, |c_min, d| d.min(c_min));
		(min_deg, max_deg)
	}).collect::<Vec<_>>();
	let g_max_deg   = degrees.iter().fold(0,          |c_max, &(_, max)| c_max.max(max));
	let g_min_deg   = degrees.iter().fold(usize::MAX, |c_min, &(min, _)| c_min.min(min));
	let max_min_deg = degrees.iter().map(|&(min, _)| min).max().unwrap_or(0);

	if degrees.iter().any(|&(min, _)| min > 100) || nodes.iter().zip(&edges).any(|(v, e)| v * 100 < *e) {
		// don't even bother
		println!("{}, {}, {}, {}, {}, {}, {}, {}", num_nodes, num_edges, components, g_max_deg, g_min_deg, max_min_deg, size_reduction, -1);
		std::process::exit(1);
	}
}
