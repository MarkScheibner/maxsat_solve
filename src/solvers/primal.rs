use crate::solver::*;
use crate::graph::Primal;
use itertools::Itertools;

impl Solve for Primal {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		// for each variable list the clauses which contain that variable as a positive / negative literal
		let occurences = formula.variable_occurences();
		
		let nice_td = make_nice(&self, td, false);
		let tree_index = tree_index(&nice_td, k, self.size());
		let traversal = traverse_order(&nice_td);
		let mut config_stack = Vec::<Vec<Configuration>>::new();
		// keep track of clauses where not all variables are active
		let mut forgotten = vec![false; formula.n_clauses];

		for i in traversal.iter() {
			let (_, node) = &nice_td[*i];
			match node {
				&Leaf => {
					// push empty configuration
					config_stack.push(vec![(0, 0, vec![])]);
				}
				&Introduce(var) => {
					let mut configs  = config_stack.pop().unwrap();

					// make duplicates of each config so we can try both values for var
					duplicate_configs(&mut configs, var, &tree_index);
					
					config_stack.push(configs);
				}
				&Forget(var) => {
					let mut configs = config_stack.pop().unwrap();

					let forget_clauses = occurences[var].iter().filter(|&&c| !forgotten[c]).collect_vec();

					// check all clauses that contain var if they are satisfied
					configs = configs.into_iter().filter_map(|(mut a, mut s, v)| {
						for clause in forget_clauses.iter() {
							// check if any variable has the desired value
							let satisfied = formula.clause(clause).iter().any(|&literal| {
								let variable  = literal.abs() as usize - 1;
								if literal > 0 {
									get_bit(&a, tree_index[variable])
								} else {
									!get_bit(&a, tree_index[variable])
								}
							});
							if satisfied {
								// clause satisfied: award points
								s += formula.soft_weight(clause);
							} else if formula.is_hard(clause) {
								// hard clause not satisfied: reject config
								return None;
							}
						}

						// reset bit of variable
						set_bit(&mut a, tree_index[var], false);

						Some((a, s, v))
					}).collect_vec();

					// mark all clauses containing var as forgotten
					forget_clauses.into_iter().for_each(|&c| forgotten[c] = true);

					deduplicate(&mut configs);

					config_stack.push(configs);
				}
				&Edge(_, _) => { /* nothing */ }
				&Join => {
					let left = config_stack.pop().unwrap();
					let right = config_stack.pop().unwrap();

					// keep only intersection of left and right
					let intersection = config_intersection(left, right);

					config_stack.push(intersection);
				}
			}
		}

		let last = config_stack.pop().unwrap();
		let (_, score, variables) = &last[0];
		let mut assignment = vec![false; formula.n_vars];
		for v in variables {
			assignment[*v] = true;
		}
		Some((assignment, *score))
	}
}

fn config_intersection(left: Vec<Configuration>, right: Vec<Configuration>) -> Vec<Configuration> {
	let max_fingerprint = left.iter().map(|(a, _, _)| a).max().unwrap();
	let mut indexes = vec![0; max_fingerprint+1];

	for (i, (a, _, _)) in left.iter().enumerate() {
		indexes[*a] = i + 1;
	}

	// since we must "guess" the same value for each variable from both sides, this is really just the intersection
	right.into_iter().filter_map(|(a, s, v)| {
		if indexes[a] > 0 {
			let (_, other_s, other_v) = &left[indexes[a] - 1];
			let combined_vars    = v.iter().chain(other_v.iter()).unique().copied().collect();
			Some((a, s + other_s, combined_vars))
		} else {
			None
		}
	}).collect_vec()
}
