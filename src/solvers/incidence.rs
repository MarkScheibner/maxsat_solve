use crate::solver::*;
use crate::graph::Incidence;
use itertools::Itertools;


impl Solve for Incidence {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let traversal        = traverse_order(&nice_td);
		let mut config_stack = Vec::<(Vec<Configuration>, usize)>::new();
		let traversal_len    = traversal.len();
		for (step, i) in traversal.into_iter().enumerate() {
			let (_, node) = &nice_td[i];
			match node {
				&Leaf => {
					// push empty configuration
					config_stack.push((vec![(0, 0, Vec::new())], 0));
				},
				&Introduce(clause) if self.is_clause(clause) => {
					let mut config = config_stack.pop().unwrap();
					// mark bit as clause
					set_bit(&mut config.1, tree_index[clause], true);

					config_stack.push(config);
				},
				&Introduce(var) => {
					let (mut config, clause_mask) = config_stack.pop().unwrap();
					duplicate_configs(&mut config, var, &tree_index);

					config_stack.push((config, clause_mask));
				},
				&Forget(clause) if self.is_clause(clause) => {
					let (mut config, mut clause_mask) = config_stack.pop().unwrap();
					reject_unsatisfied(&mut config, clause, &tree_index, &formula);

					// unmark clause-bit
					set_bit(&mut clause_mask, tree_index[clause], false);
					deduplicate(&mut config);
					
					config_stack.push((config, clause_mask));
				},
				&Forget(var) => {
					let (mut config, clause_mask) = config_stack.pop().unwrap();
					for (a, _, _) in &mut config {
						// unset bit of variable
						set_bit(a, tree_index[var], false);
					}
					deduplicate(&mut config);
					
					config_stack.push((config, clause_mask));
				},
				&Edge(u, v)  => {
					let (mut config, clause_mask) = config_stack.pop().unwrap();
					let clause                    = if u < v { u } else { v };
					let var                       = if u < v { v } else { u };
					let negated                   = var == u;

					for (a, _, _) in &mut config {
						// set clause to true if the literal represented by the edge is true
						let literal = if negated { !get_bit(a, tree_index[var]) } else { get_bit(a, tree_index[var]) };
						if literal {
							set_bit(a, tree_index[clause], true);
						}
					}
					deduplicate(&mut config);

					config_stack.push((config, clause_mask));
				},
				&Join => {
					let (left_config, clauses) = config_stack.pop().unwrap();
					let (right_config, _)      = config_stack.pop().unwrap();
					
					let intersection           = config_intersection(left_config, right_config, clauses);
					
					config_stack.push((intersection, clauses));
				}
			}

			if config_stack.last().map_or(true, |(config, _)| config.is_empty()) {
				println!("No solution found after {}/{} steps", step, traversal_len);
				return None;
			}
		}

		let last           = config_stack.pop().unwrap();
		let (_, score, variables) = &last.0[0];
		let mut assignment = vec![false; formula.n_vars];
		for v in variables {
			let variable_index = v - formula.n_clauses;
			assignment[variable_index] = true;
		}
		Some((assignment, *score))
	}
}

fn reject_unsatisfied(config: &mut Vec<Configuration>, clause: usize, tree_index: &Vec<usize>, f: &Formula) {
	let mut rejected = vec![];

	for (i, (a, s, _)) in config.iter_mut().enumerate() {
		if get_bit(a, tree_index[clause]) {
			// clause is true: unset bit and update score
			set_bit(a, tree_index[clause], false);
			*s += if f.is_hard(&clause) { 0 } else { f.weight(&clause) };
		} else if f.is_hard(&clause) {
			// clause is not true, but is a hard clause: reject assignment
			rejected.push(i);
		}
	}
	
	// remove rejected configs
	rejected.reverse();
	for i in rejected {
		config.swap_remove(i);
	}
}

fn config_intersection(left: Vec<Configuration>, right: Vec<Configuration>, clauses: usize) -> Vec<Configuration> {
	let _min_fingerprint = left.iter().map(|(a, _, _)| a & !clauses).max().unwrap();
	let max_fingerprint = left.iter().map(|(a, _, _)| a & !clauses).max().unwrap();

	let mut indexes     = vec![vec![]; max_fingerprint+1];
	for (i, (a, _ , _)) in left.iter().enumerate() {
		// we only care about assignment of variables here.
		let variable_assignment = a & !clauses;
		indexes[variable_assignment].push(i);
	}
	// keep only those variable assignments that are in left and in right
	right.into_iter().filter_map(|(a, s, v)| {
		let variable_assignment = a & !clauses;
		if variable_assignment > max_fingerprint || indexes[variable_assignment].is_empty() {
			None
		} else {
			// since an assignment can have different values for clauses (due to forgotten variables) we need to look
			// at the bitwise OR of every such clause assignment
			let mut bitwise_or = Vec::with_capacity(indexes[variable_assignment].len());
			for &other_index in &indexes[variable_assignment] {
				let (other_a, other_s, other_v) = &left[other_index];
				bitwise_or.push((a | other_a, s + other_s, v.iter().chain(other_v.iter()).unique().copied().collect()));
			}
			Some(bitwise_or)
		}
	}).flatten().collect()
}