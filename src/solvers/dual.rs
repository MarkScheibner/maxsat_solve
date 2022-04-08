use std::collections::VecDeque;

use crate::solver::*;
use crate::graph::Dual;
use itertools::Itertools;

type Set<T>        = metrohash::MetroHashSet<T>;
type OccurenceList = Vec<(Set<usize>, Set<usize>)>;
type ConfigTable   = Vec<Option<(usize, Vec<usize>)>>;

#[derive(Clone, Default)]
struct VirtualBag {
	vars:    Set<usize>,
	clauses: Vec<usize>
}

impl Solve for Dual {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let var_index        = var_index(&nice_td, &formula);
		let traversal        = traverse_order(&nice_td);

		let v_bags           = virtual_bag_marking(&nice_td, &traversal, &formula);

		let mut config_stack = Vec::<Vec<Configuration>>::new();

		for i in traversal.into_iter() {
			let (_, node) = &nice_td[i];
			match node {
				Leaf => {
					config_stack.push(vec![(0, 0, vec![])]);
				},
				&Forget(clause) => {
					let configs = config_stack.pop().unwrap();
					let v_bag   = &v_bags[clause];

					let mut config_table = vec![None; 1 << k];
					make_sufficient_list(&mut config_table, &v_bag, configs, &tree_index, &formula, &var_index);

					// compress table into vec
					let mut configs = compress_table(config_table);
					// simplify_configs(&mut configs, k);

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

					let configs = compress_table(config_table);
					// simplify_configs(&mut configs, k);

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

fn var_index(nice_td: &Vec<(usize, Node)>, formula: &Formula) -> Vec<usize>{
	let mut var_index = vec![0; formula.n_vars];
	let mut free      = vec![true; formula.n_vars];
	let traversal     = traverse_order(nice_td);
	for i in traversal {
		let (_, node) = nice_td[i];
		if let Forget(clause) = node {
			let literals = formula.clause(&clause);
			let vars     = literals.iter().map(|l| l.abs() as usize - 1).filter(|v| free[*v]).collect_vec();
			for (i, v) in vars.into_iter().enumerate() {
				free[v] = false;
				var_index[v] = i;
			}
			
		}
	}

	var_index
}
fn virtual_bag_marking(nice_td: &NiceDecomposition, traversal: &Vec<usize>, f: &Formula) -> Vec<VirtualBag> {
	let occurences = f.variable_occurences();
	let mut free   = vec![true; f.n_vars];
	let mut v_bags = vec![VirtualBag::default(); f.n_clauses];

	for &i in traversal {
		if let Forget(clause) = &nice_td[i].1 {
			// set of vars of clause that are still free
			let vars: Set<usize> = f.clause(clause).iter().map(|l| l.abs() as usize - 1).filter(|v| free[*v]).collect();
			// list clauses that share a free variable with clause
			let clauses          = vars.iter().flat_map(|v| occurences[*v].clone()).unique().collect_vec();

			let v_bag = VirtualBag {
				vars,
				clauses
			};
			
			// lock all variables of clause
			for v in &v_bag.vars {
				free[*v] = false;
			}

			v_bags[*clause] = v_bag;
		}
	}

	v_bags
}

fn partitioned_occurence_list(clauses: &Vec<usize>, formula: &Formula, vars: &Set<usize>, var_index: &Vec<usize>) -> OccurenceList {
	let mut occ_list = vec![(Set::<usize>::default(), Set::<usize>::default()); vars.len()];
	for &c in clauses.iter() {
		for &l in formula.clause(&c) {
			let var = l.abs() as usize - 1;
			if !vars.contains(&var) { continue; }
			if l < 0 {
				occ_list[var_index[var]].0.insert(c);
			} else {
				occ_list[var_index[var]].1.insert(c);
			}
		}
	}

	occ_list
}


fn make_sufficient_list(table: &mut ConfigTable, v_bag: &VirtualBag, configs: Vec<Configuration>, tree_index: &Vec<usize>, f: &Formula, var_index: &Vec<usize>) {
	let vars    = &v_bag.vars;
	let clauses = &v_bag.clauses;
	
	let mut tree_stack = vec![(0, 0, partitioned_occurence_list(&clauses, &f, &vars, &var_index))];
	let mut leafs      = vec![];

	while let Some((mut c, mut v, mut occ)) = tree_stack.pop() {
		unpurify(&mut occ, &vars, &mut c, &mut v, &tree_index, &var_index);

		// get next free variable.
		let next = vars.iter().find(|v| {
			let v_index = var_index[**v];
			// product is 0 -> variable is pure or removed
			occ[v_index].0.len() * occ[v_index].1.len() != 0
		});

		if let Some(&var) = next {
			// set var to 0
			let mut c_0   = c.clone();
			let v_0       = v.clone();
			let mut occ_0 = occ.clone();
			for &c in &occ[var_index[var]].0 {
				// c is satisfied when var is 0
				set_bit(&mut c_0, tree_index[c], true);
				delete_clause_from_occ(&mut occ_0, &c, &vars, &var_index);
			}
			// remove unsatisfied literals
			occ_0[var_index[var]].1 = Set::default();

			// set var to 1
			let mut c_1   = c.clone();
			let v_1       = v.clone() | 1 << var_index[var];
			let mut occ_1 = occ.clone();
			for &c in &occ[var_index[var]].1 {
				// c is satisfied when var is 1
				set_bit(&mut c_1, tree_index[c], true);
				delete_clause_from_occ(&mut occ_1, &c, &vars, &var_index);
			}
			// remove unsatisfied literals
			occ_1[var_index[var]].0 = Set::default();

			tree_stack.push((c_0, v_0, occ_0));
			tree_stack.push((c_1, v_1, occ_1));
		} else {
			// no variable left
			leafs.push((c, v));
		}
	}
	
	for (c_bits, v_bits) in leafs {
		for (c, s, v) in configs.iter() {
			let new_assignment = c | c_bits;
			let other          = &table[new_assignment];
			// only override the entry if it is either empty or has a lower score
			let overwrite      = other.is_none() || matches!(other, Some((other_s, _)) if *other_s < *s);
			
			if overwrite {
				let mut v = v.clone();
				v.extend(extract_vars(v_bits, &vars, &var_index));
				table[new_assignment] = Some((*s, v));
			}
		}
	}

}

fn compress_table(table: ConfigTable) -> Vec<Configuration> {
	table.into_iter().enumerate().filter_map(|(i, c)| {
		c.map(|(s, v)| (i, s, v))
	}).collect()
}

fn unpurify(occ: &mut OccurenceList, vars: &Set<usize>, c_mask: &mut usize, v_mask: &mut usize,
            tree_index: &Vec<usize>, var_index: &Vec<usize>) {
	let pure = vars.iter()
	               .filter(|v| occ[var_index[**v]].0.len() == 0 || occ[var_index[**v]].1.len() == 0)
	               .filter(|v| occ[var_index[**v]].0.len() != occ[var_index[**v]].1.len())
	               .map(|v| (*v, occ[var_index[*v]].0.len() == 0)) // if no negative occurence -> v is positive
	               .collect_vec();
	let mut pure = VecDeque::from(pure);

	// while there is some pure variable, lock its value
	while let Some((v, v_value)) = pure.pop_front() {
		let v_index = var_index[v];
		// set value of v in bitmask
		set_bit(v_mask, v_index, v_value);

		// get set of clauses containing pure variable. they are now satisfied
		let satisfied_clauses = if v_value { occ[v_index].1.clone() } else { occ[v_index].0.clone() };
		// clear sets of variable
		for c in satisfied_clauses {
			set_bit(c_mask, tree_index[c], true);
			// delete clause and find new pure variables
			let new_pure = delete_clause_from_occ(occ, &c, vars, var_index);
			pure.extend(new_pure.into_iter());
		}
		occ[v_index] = (Set::default(), Set::default());
	}
}
fn delete_clause_from_occ(occ: &mut OccurenceList, c: &usize, vars: &Set<usize>, var_index: &Vec<usize>) -> Vec<(usize, bool)> {
	let mut new_pure = vec![];
	for &v in vars {
		let v_index = var_index[v];
		// check if v is already pure
		let skip = occ[v_index].0.len() == 0 || occ[v_index].1.len() == 0;

		occ[v_index].0.remove(c);
		occ[v_index].1.remove(c);
		
		// we already know that v became pure
		if skip { continue; }

		if occ[v_index].0.len() == 0 && occ[v_index].1.len() != 0 {
			new_pure.push((v, true));
		} else if occ[v_index].0.len() == 0 && occ[v_index].1.len() != 0  {
			new_pure.push((v, false));
		}
	}

	new_pure
}
fn extract_vars(var_bits: usize, vars: &Set<usize>, var_index: &Vec<usize>) -> Vec<usize> {
	vars.iter().filter(|v| get_bit(&var_bits, var_index[**v])).map(|v| *v).collect_vec()
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
	let max_score = *configs.iter().map(|(_, s, _)| s).max().unwrap();

	for (c, s, v) in configs.clone() {
		// if all k bits are set and we have the best score we have no reason to do anything else
		if c == ((1 << k) - 1) && s == max_score {
			*configs = vec![(c, s, v)];
			break;
		}
	}
}