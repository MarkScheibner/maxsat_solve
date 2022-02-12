use std::collections::VecDeque;

use crate::solver::*;
use crate::graph::Dual;
use itertools::Itertools;

type Set<T>        = metrohash::MetroHashSet<T>;
type OccurenceList = Vec<(Set<usize>, Set<usize>)>;

impl Solve for Dual {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let var_index        = var_index(&nice_td, &formula);
		let traversal        = traverse_order(&nice_td);
		let mut config_stack = Vec::<Vec<Configuration>>::new();
		
		let occurences = formula.variable_occurences();
		let mut free   = vec![true; formula.n_vars];

		for i in traversal.into_iter() {
			let (_, node) = &nice_td[i];
			match node {
				Leaf => {
					config_stack.push(vec![(0, 0, vec![])]);
				},
				Forget(clause) => {
					let configs    = config_stack.pop().unwrap();
					let clause_bit = tree_index[*clause]; 

					// set of vars of clause that are still free
					let vars: Set<usize> = formula.clause(clause).iter().map(|l| l.abs() as usize - 1)
					                                                    .filter(|v| free[*v])
					                                                    .collect();
					// list clauses that share a free variable with clause
					let clauses          = vars.iter().flat_map(|v| occurences[*v].clone()).unique().collect_vec();

					// split configurations into those where clause is already satisfied and those where its not
					let (sat, unsat): (Vec<_>, Vec<_>) = configs.into_iter()
					                                            .partition(|(a, _, _)| get_bit(a, clause_bit));
					
					/* TODO
					// table for all 2^k possible clause configurations
					let mut config_table: ConfigTable = vec![None; 1 << k];
					if !formula.is_hard(clause) {
						make_nonsat_configs(&mut config_table, ...);
					}
					make_sat_configs(&mut config_table, ...);
					configs = compress_table(config_table);
					*/

					// list those variables, which have to be set to 1 in order to not satisfy clause
					let nonsat_assignment: Set<_> = formula.clause(clause).iter()
					                                                      .filter(|l| **l < 0)
					                                                      .map(|l| l.abs() as usize - 1)
					                                                      .collect();
					// list clauses that become satisfied when clause is not satisfied
					let nonsat_clauses = clauses.iter().filter(|c| {
						formula.clause(c).iter().any(|&l| {
							let var = l.abs() as usize - 1;
							// we only care for variables that are in clause
							if !vars.contains(&var) { return false; }
							// evaluate literal
							if l > 0 {
								nonsat_assignment.contains(&var)
							} else {
								!nonsat_assignment.contains(&var)
							}
						})
					});
					// make bitmask for setting bits of now satsfied clauses
					let mut nonsat_bitmask = 0;
					for &c in nonsat_clauses {
						set_bit(&mut nonsat_bitmask, tree_index[c], true);
					}
					// build configs where clause is not satisfied
					let nonsat_configs = unsat.clone().into_iter().map(|(a, s, mut v)| {
						let new_assignment = a | nonsat_bitmask;
						v.extend(nonsat_assignment.clone());
						(new_assignment, s, v)
					});
					let sat_configs   = {
						// configs, where clause is already satisfied and will not be satisfied by any of vars
						let already_sat = sat.clone().into_iter().map(|(a, s, mut v)| {
							let new_assignment = a | nonsat_bitmask;
							v.extend(nonsat_assignment.clone());
							(new_assignment, s, v)
						});
						// configs, where clause becomes satisfied (even if it already is) by one of vars
						let newly_sat = {
							let mut sat_configs = vec![];
							// build occurence list. for v we have c in the left set if c contains ¬v and in the right
							// set if c contains v
							let mut occ_list = partitioned_occurence_list(&clauses, &formula, &vars, &var_index);

							for v in vars.iter() {
								let mut clause_assignment = 0;
								let mut var_assignment    = 0;
								// do the opposite of the nonsat assignment
								let v_value = !nonsat_assignment.contains(&v);
								let v_index = var_index[*v];
								// all clauses that agree with clause on v became satisfied
								let satisfied_clauses = if !v_value {
									&occ_list[v_index].0
								} else {
									&occ_list[v_index].1
								};
								for c in satisfied_clauses.clone() {
									// mark satisfied clauses
									set_bit(&mut clause_assignment, tree_index[c], true);
									// mark v with its values
									set_bit(&mut var_assignment, var_index[*v], v_value);
									// remove clause from occ_list and empty entries for var
									occ_list[v_index] = (Set::default(), Set::default());
									delete_clause_from_occ(&mut occ_list, &c, &vars, &var_index);
								}

								let mut tree_stack = vec![(clause_assignment, var_assignment, occ_list.clone())];
								let mut leafs      = vec![];
								

								while let Some((mut c, mut v, mut occ)) = tree_stack.pop() {
									unpurify(&mut occ, &vars, &mut c, &mut v, &tree_index, &var_index);

									// get next free variable
									let next = vars.iter().find(|v| {
										let v_index = var_index[**v];
										// produce is 0 -> variable is pure or removed
										occ_list[v_index].0.len() * occ_list[v_index].1.len() != 0
									});

									if let Some(&var) = next {
										// make copies to mutate for when var is 0
										let mut c_0   = c.clone();
										let v_0       = v | 1 << var_index[var];
										let mut occ_0 = occ.clone();
										// copies for when var is 1
										let mut c_1   = c.clone();
										let v_1       = v.clone();
										let mut occ_1 = occ.clone();
	
										for &c in clauses.iter() {
											if occ_list[var_index[var]].0.contains(&c) {
												// c is satisfied when var is 0
												set_bit(&mut c_0, tree_index[c], true);
												delete_clause_from_occ(&mut occ_0, &c, &vars, &var_index);
											} else if occ_list[var_index[var]].1.contains(&c) {
												// c is satisfied when var is 1
												set_bit(&mut c_1, tree_index[c], true);
												delete_clause_from_occ(&mut occ_1, &c, &vars, &var_index);
											}
										}
	
										tree_stack.push((c_0, v_0, occ_0));
										tree_stack.push((c_1, v_1, occ_1));
									} else {
										// no variable left
										leafs.push((c, v));
									}
								}

								let weight = if formula.is_hard(clause) { 0 } else { formula.weight(clause) };
								for (c, v_bits) in leafs.into_iter() {
									for (a, s, v) in sat.iter().chain(unsat.iter()) {
										let mut combined_vars = v.clone();
										combined_vars.extend(extract_vars(v_bits, &vars, &var_index));
										sat_configs.push((a | c, s + weight, v.clone()));
									}
								}

							}

							sat_configs
						};

						// configs where clause becomes satisfied
						already_sat.into_iter().chain(newly_sat.into_iter()).collect_vec()
					};

					// merge configs
					let mut configs = if formula.is_hard(clause) {
						// nonsat configs are rejected
						sat_configs
					} else {
						// nonsat configs are allowed
						nonsat_configs.into_iter().chain(sat_configs.into_iter()).collect_vec()
					};

					// unset bit
					for (a, _, _) in configs.iter_mut() {
						set_bit(a, clause_bit, false);
					}
					
					// remove duplicate configs
					deduplicate(&mut configs);

					// lock all variables of clause
					for v in vars {
						free[v] = false;
					}

					config_stack.push(configs);
				},
				Join => {
					let left        = config_stack.pop().unwrap();
					let right       = config_stack.pop().unwrap();
					let combined    = left.into_iter().cartesian_product(right.into_iter());
					let mut configs = combined.map(|((a1, s1, v1), (a2, s2, v2))| {
						let combined_assignment = a1 | a2;
						let combined_score      = s1 + s2;
						// TODO we can save ourselves some work here if we do the deduplication here
						let combined_vars       = v1.into_iter().chain(v2.into_iter()).unique().collect_vec();
						(combined_assignment, combined_score, combined_vars)
					}).collect_vec();

					deduplicate(&mut configs);

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