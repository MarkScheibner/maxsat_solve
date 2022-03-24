use crate::solver::*;
use crate::graph::Dual;
use itertools::Itertools;

type BitmaskList = Vec<(usize, usize)>;
type ConfigTable = Vec<Option<(usize, Vec<usize>)>>;

impl Solve for Dual {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let traversal        = traverse_order(&nice_td);

		let variable_marking = variable_marking(&nice_td, &traversal, &formula);
		let variable_masks   = bitmask_list(&formula, &tree_index);

		let mut config_stack = Vec::<Vec<Configuration>>::new();

		for i in traversal.into_iter() {
			let (_, node) = &nice_td[i];
			match node {
				Leaf => {
					config_stack.push(vec![(0, 0, vec![])]);
				},
				&Forget(clause) => {
					let configs    = config_stack.pop().unwrap();
					let vars       = &variable_marking[i];
					
					let mut config_table = make_table(configs, k);

					for variable in vars {
						// virtually introduce v and corresponding edges and immediately forget v again
						virtual_introduce(&mut config_table, *variable, &variable_masks);
					}
					
					// compress table into vec
					let mut configs = compress_table(config_table);
					
					simplify_configs(&mut configs, k);

					reject_unsatisfied(&mut configs, clause, &tree_index, &formula);

					config_stack.push(configs);
				},
				Join => {
					let left             = config_stack.pop().unwrap();
					let right            = config_stack.pop().unwrap();
					let mut config_table = vec![None; 1 << k];
					for (a1, s1, v1) in left {
						for (a2, s2, v2) in right.iter() {
							let combined_assignment = a1 | a2;
							let replace = match config_table[combined_assignment] {
								Some((other_s, _)) => other_s < s1 + s2,
								None               => true
							};

							if replace {
								let v1 = v1.clone();
								let v2 = v2.clone();
								let combined_vars = v1.into_iter().chain(v2.into_iter()).unique().collect_vec();
								config_table[combined_assignment] = Some((s1 + s2, combined_vars));
							}
						}
					}

					let mut configs = compress_table(config_table);
					simplify_configs(&mut configs, k);

					config_stack.push(configs);
				},
				// Introduce and Edge do nothing
				_ => {}
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

fn variable_marking(nice_td: &NiceDecomposition, traversal: &Vec<usize>, f: &Formula) -> Vec<Vec<usize>> {
	let mut free    = vec![true; f.n_vars];
	let mut marking = vec![vec![]; nice_td.len()];

	for &i in traversal {
		if let Forget(clause) = &nice_td[i].1 {
			// set of vars for which we break the variable clique
			let vars   = f.clause(clause).iter().map(|l| l.abs() as usize - 1).filter(|v| free[*v]).collect_vec();
			vars.iter().for_each(|v| free[*v] = false);
			marking[i] = vars;
		}
	}

	marking
}

fn bitmask_list(formula: &Formula, tree_index: &Vec<usize>) -> BitmaskList {
	let mut bitmask_list = vec![(0, 0); formula.n_vars];
	for c in 0..formula.n_clauses {
		for &l in formula.clause(&c) {
			let var = l.abs() as usize - 1;
			if l < 0 {
				set_bit(&mut bitmask_list[var].0, tree_index[c], true);
			} else {
				set_bit(&mut bitmask_list[var].1, tree_index[c], true);
			}
		}
	}

	bitmask_list
}

fn virtual_introduce(config_table: &mut ConfigTable, variable: usize, bitmasks: &BitmaskList) {
	let bitmask_0 = bitmasks[variable].0;
	let bitmask_1 = bitmasks[variable].1;

	// we need to iterate in reverse order so we dont override configs from last virtual_introduce before we got the
	// chance to use them
	for i in (0..config_table.len()).rev() {
		if let Some((s, v)) = config_table[i].clone() {
			// configuration from last virtual_introduce and thus no longer valid. delete.
			config_table[i] = None;

			// config with variable set to 1
			let a_1 = i | bitmask_1;
			let mut v_1 = v.clone();
			v_1.push(variable);
			insert_to_table(config_table, (a_1, s, v_1));

			// config with variable set to 0
			let a_0 = i | bitmask_0;
			insert_to_table(config_table, (a_0, s, v));
		}
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

fn simplify_configs(configs: &mut Vec<Configuration>, k: usize) {
	// optimization: if there is a configuration that satisfies all clauses and that configuration has
	// optimal score, then we can keep only that configuration
	let max_score = *configs.iter().map(|(_, s, _)| s).max().unwrap();

	for (c, s, v) in configs.clone() {
		// if all k bits are set and we have the best score we have no reason to do anything else
		if c == ((1 << k) - 1) && s == max_score {
			*configs = vec![(c, s, v)];
			break;
		}
	}
}

fn make_table(configs: Vec<Configuration>, k: usize) -> ConfigTable {
	let mut table = vec![None; 1 << k];
	for (a, s, v) in configs {
		table[a] = Some((s, v));
	}

	table
}
fn insert_to_table(table: &mut ConfigTable, config: Configuration) {
	let (a, s, v) = config;
	if let Some((other_s, _)) = table[a] {
		if other_s < s {
			table[a] = Some((s, v));
		}
	} else {
		table[a] = Some((s, v));
	}
}
fn compress_table(table: ConfigTable) -> Vec<Configuration> {
	table.into_iter().enumerate().filter_map(|(i, c)| {
		c.map(|(s, v)| (i, s, v))
	}).collect()
}