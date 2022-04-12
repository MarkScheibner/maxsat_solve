// use std::io::Write;
use std::{fs, io::{self, Read}};
use itertools::Itertools;
// use fasttw::print;
use pico_args::Arguments;
use rand::{ rngs::StdRng, SeedableRng };
use solver::Solve;

mod parser;
mod graph;
mod fasttw;
mod solver;
mod solvers;

use crate::parser::Formula;
use crate::graph::Graph;

type Assignment    = Vec<bool>;
type OptAssignment = Vec<Option<bool>>;
type Renaming      = Vec<usize>;

fn main() -> anyhow::Result<()>{
	// get file name for WCNF file
	let mut args                  = Arguments::from_env();
	let file_name: Option<String> = args.value_from_str("--file").or_else(|_| args.value_from_str("-f")).ok();
	// read contents from file or stdin depending on command line arguments
	let mut contents = String::new();
	let mut reader: Box<dyn std::io::Read> = match file_name {
		Some(file_name) => Box::new(fs::File::open(file_name)?),
		None            => Box::new(io::stdin())
	};
	// decompress if needed
	if args.contains("-c") || args.contains("--compressed") {
		reader = Box::new(flate2::read::GzDecoder::new(reader));
	}
	reader.read_to_string(&mut contents)?;

	// parse, preprocess and split formula
	let mut formula               = parser::Formula::from(contents);
	let copy = formula.clone();
	let max_score                 = formula.max_score();
	let size_before               = formula.n_clauses;
	let preprocess_result         = formula.preprocess();
	let _size_reduction           = size_before - formula.n_clauses;
	let (sub_formulas, renamings) = formula.split();
	
	let use_primal = args.contains("-p") || args.contains("--primal");
	let use_dual   = args.contains("-d") || args.contains("--dual");
	
	// get variable assignment for each subformula
	let sub_assignments = if use_primal {
		solve_formulas::<graph::Primal>(sub_formulas)
	} else if use_dual {
		solve_formulas::<graph::Dual>(sub_formulas)
	} else {
		solve_formulas::<graph::Incidence>(sub_formulas)
	};

	// undo local renamings and merge solutions
	match sub_assignments.zip(preprocess_result) {
		Some(((solutions, score), (assignment, renaming, s))) => {
			let merged = merge_solutions(solutions, renamings);
			let assignment = unpack_solution(assignment, merged, renaming);
			println!("c max: {}, pre: {}, solver: {}", max_score, s, score);
			if args.contains("-t") || args.contains("--test") {
				println!("c Testing assignment gives: {:?}", copy.test_assignment(&assignment));
			}
			
			println!("s OPTIMUM FOUND");
			println!("o {}", max_score - (score + s));
			println!("v {}", format_assignment(assignment));
		},
		None => {
			println!("s UNSATISFIABLE");
		}
	}
	
	Ok(())
}

fn solve_formulas<T>(sub_formulas: Vec<Formula>) -> Option<(Vec<Assignment>, usize)> 
where T: Solve + Graph + From<Formula> + std::fmt::Debug {
	let mut rng         = StdRng::seed_from_u64(crate::fasttw::SEED);
	let mut assignments = Vec::with_capacity(sub_formulas.len());
	let mut score       = 0;

	for formula in sub_formulas.into_iter() {
		let f_copy                  = formula.clone();
		let graph                   = T::from(formula);

		// build treedecomposition
		let mut decomposition_graph = fasttw::Graph::new(graph.size());
		graph.list_edges().iter().for_each(|(u, v)| decomposition_graph.add_edge(*u, *v));
		let peo = decomposition_graph.compute_peo(&mut rng);
		let td  = decomposition_graph.peo_to_decomposition(&peo)?;

		// solve instance
		let k        = td.iter().map(|(_, bag)| bag.len()).max().unwrap_or(0);
		let solution = graph.solve(td, k, f_copy)?;

		// add to other solutions
		assignments.push(solution.0);
		score += solution.1;
	}

	Some((assignments, score))
}

fn merge_solutions(solutions: Vec<Assignment>, renamings: Vec<Renaming>) -> Assignment {
	let mut assignment = vec![false; solutions.iter().map(|s| s.len()).sum()];

	for (local_solution, local_renaming) in solutions.into_iter().zip(renamings.into_iter()) {
		for (local_var, value) in local_solution.into_iter().enumerate() {
			// undo renaming on local_var
			let global_index = local_renaming[local_var] - 1;
			assignment[global_index] = value;
		}
	}

	assignment
}
fn unpack_solution(pre_assignment: OptAssignment, solution: Assignment, renaming: Renaming) -> Assignment {
	let mut assignment = pre_assignment.into_iter().map(|v| v.unwrap_or(false)).collect_vec();
	for (renamed_var, value) in solution.into_iter().enumerate() {
		let global_index         = renaming[renamed_var] - 1;
		assignment[global_index] = value;
	}

	assignment
}
fn format_assignment(assignment: Assignment) -> String {
	assignment.into_iter().enumerate().map(|(i, v)| {
		let variable_name = i as isize +1;
		if v { variable_name } else {-variable_name }
	}).join(", ")
}
