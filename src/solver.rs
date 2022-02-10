use std::collections::VecDeque;

use itertools::Itertools;
use metrohash::{MetroHashSet, MetroHashMap};


use crate::graph::*;
use crate::fasttw::Decomposition;

type Set<T>    = MetroHashSet<T>;
type Map<K, V> = MetroHashMap<K, V>;

type Assignment = Vec<bool>;
type NiceDecomposition = Vec<(usize, Node)>;
// assignment (bit-map), score, true variables
type Configuration = (usize, usize, Vec<usize>);
type ConfigTable = Vec<Option<(usize, Vec<usize>)>>;
type OccurenceList = Vec<(Set<usize>, Set<usize>)>;

#[derive(Clone, Copy, Debug)]
enum Node {
	Leaf,
	Introduce(usize),
	Forget(usize),
	Edge(usize, usize),
	Join
}
use crate::parser::Formula;
use crate::solver::Node::*;

pub trait Solve {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)>;
}

impl Solve for Primal {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		//println!("{:?}", &td);
		
		// for each variable list the clauses which contain that variable as a positive / negative literal
		let occurences = formula.variable_occurences();
		
		let nice_td = make_nice(&self, td, false);
		let tree_index = tree_index(&nice_td, k, formula.n_vars);
		let traversal = postorder(&nice_td);
		let mut config_stack = Vec::<Vec<Configuration>>::new();
		// keep track of clauses where not all variables are active
		let mut forgotten = vec![false; formula.n_clauses]; // TODO make this a bitvec
		for i in traversal.iter() {
			let (_, node) = &nice_td[*i];
			match node {
				&Leaf => {
					// push empty configuration
					config_stack.push(vec![(0, 0, vec![])]);
				}
				&Introduce(var) => {
					let mut configs  = config_stack.pop().unwrap();

					// clone configs and set bit for var to 1
					let clones = configs.iter().cloned().map(|(mut a, s, mut v)| {
						set_bit(&mut a, tree_index[var], true);
						v.push(var);

						(a, s, v)
					}).collect_vec();
					
					configs.extend(clones);
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

					let max_fingerprint = left.iter().map(|(a, _, _)| a).max().unwrap();
					let mut indexes = vec![0; max_fingerprint+1];

					for (i, (a, _, _)) in left.iter().enumerate() {
						indexes[*a] = i + 1;
					}

					// keep only intersection of left and right
					let intersection = right.iter().filter_map(|(a, s, v)| {
						if indexes[*a] > 0 {
							let (_, other_s, other_v) = &left[indexes[*a] - 1];
							let combined_vars    = v.iter().chain(other_v.iter()).unique().copied().collect();
							Some((*a, s + other_s, combined_vars))
						} else {
							None
						}
					}).collect_vec();

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


impl Solve for Dual {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let var_index        = var_index(&nice_td, &formula);
		let traversal        = postorder(&nice_td);
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

impl Solve for Incidence {
	fn solve(self, td: Decomposition, k: usize, _formula: Formula) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td, true);
		
		let tree_index       = tree_index(&nice_td, k, self.size());
		let traversal        = postorder(&nice_td);
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
					duplicate_assignments(&mut config, var, &tree_index);

					config_stack.push((config, clause_mask));
				},
				&Forget(clause) if self.is_clause(clause) => {
					let (mut config, mut clause_mask) = config_stack.pop().unwrap();
					reject_unsatisfied(&mut config, clause, &tree_index, &self);

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
		let mut assignment = vec![false; self.size() - self.num_clauses];
		for v in variables {
			let variable_index = v - self.num_clauses;
			assignment[variable_index] = true;
		}
		Some((assignment, *score))
	}
}

fn duplicate_assignments(config: &mut Vec<Configuration>, var: usize, tree_index: &Vec<usize>) {
	let  mut copies = Vec::with_capacity(config.len());

	// duplicate each assignment and set var to true in copy
	for (a, s, v) in config.iter_mut() {
		let mut copy   = a.clone();
		set_bit(&mut copy, tree_index[var], true);
		let mut v_copy = v.clone();
		v_copy.push(var);
		copies.push((copy, *s, v_copy));
	}
	// append copies to config
	config.extend(copies);
}
fn reject_unsatisfied(config: &mut Vec<Configuration>, clause: usize, tree_index: &Vec<usize>, graph: &Incidence) {
	let mut rejected = vec![];

	for (i, (a, s, _)) in config.iter_mut().enumerate() {
		if get_bit(a, tree_index[clause]) {
			// clause is true: unset bit and update score
			set_bit(a, tree_index[clause], false);
			*s += if graph.is_hard(clause) { 0 } else { graph.weight(clause) };
		} else if graph.is_hard(clause) {
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
fn deduplicate(config: &mut Vec<Configuration>) {
	let max_fingerprint = config.iter().map(|(a, _, _)| a).max().unwrap();
	// we should save every byte possible here, so we also use usize instead of Option<usize>
	// for this we use 0 as None and i+1 as Some(i)
	let mut indexes     = vec![0; max_fingerprint+1];
	for (i, &(a, s, _)) in config.iter().enumerate() {
		if indexes[a] == 0 { // None
			indexes[a] = i+1;
		} else {             // Some(i+1)
			if config[indexes[a] - 1].1 < s {
				// this one is better
				indexes[a] = i+1
			}
		}
	}

	// deduplicate
	for i in (0..config.len()).rev() {
		let fingerprint = config[i].0;
		if indexes[fingerprint] != i+1 {
			// if an assignment does not find its own index, another assignment with the same
			// fingerprint had a better score, so we can remove this assigmnent
			config.swap_remove(i);
		}
	}
}
fn config_intersection(left: Vec<Configuration>, right: Vec<Configuration>, clauses: usize) -> Vec<Configuration> {
	let max_fingerprint = left.iter().map(|(a, _, _)| a & !clauses).max().unwrap();
	let mut indexes     = vec![Vec::new(); max_fingerprint+1];
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

fn var_index(nice_td: &Vec<(usize, Node)>, formula: &Formula) -> Vec<usize>{
	let mut var_index = vec![0; formula.n_vars];
	let mut free      = vec![true; formula.n_vars];
	let traversal     = postorder(nice_td);
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

fn make_nice(graph: &impl Graph, td: Decomposition, very_nice: bool) -> NiceDecomposition {
	enum Work<'a> {
		// parent node, children
		Join(usize,  &'a [usize]),
		// parent node, child
		Stretch(usize, usize),
		// parent node, leaf-bag
		Empty(usize, usize)
	}
	
	let mut nice_decomposition = Vec::new();
	let (root, children) = reverse(&td);

	let mut work_queue = VecDeque::new();
	work_queue.push_back(Work::Stretch(0, root));

	while let Some(work) = work_queue.pop_front() {
		match work {
			Work::Join(parent, children) => {
				// this is where the join node will be placed
				let this_node = nice_decomposition.len();
				if children.len() == 2 {
					// join left and right
					nice_decomposition.push((parent, Join));

					// only two children remain, no further joins needed. stretch left and right from join-bag
					work_queue.push_back(Work::Stretch(this_node, children[0]));
					work_queue.push_back(Work::Stretch(this_node, children[1]));
				} else {
					// join the following join node and the following stretch
					nice_decomposition.push((parent, Join));

					// join children except for the last
					work_queue.push_back(Work::Join(this_node, &children[0..children.len()-1]));
					// stretch from Join-root to last child
					work_queue.push_back(Work::Stretch(this_node, *children.last().unwrap()));
				}
			}
			Work::Stretch(mut parent, child) => {
				// while we stretch from the parent to its child, we actually add and remove from the child
				let (parent_bag, src_bag) = &td[child];
				let dest_bag              = if child == root { &[] } else { td[*parent_bag].1.as_slice() };

				// find out which nodes to introduce (add) or forget (remove) if moving from src_bag to dest_bag
				let add    = dest_bag.into_iter().filter(|v| !src_bag.contains(v)).collect_vec();
				let remove = src_bag.into_iter().filter(|v| !dest_bag.contains(v)).collect_vec();

				for &introduce in add {
					nice_decomposition.push((parent, Introduce(introduce)));
					parent = nice_decomposition.len() - 1;
				}
				for &forget in remove {
					nice_decomposition.push((parent, Forget(forget)));
					parent = nice_decomposition.len() - 1;
					if very_nice {
						// add all edges that are incident to forget
						for &node in src_bag {
							// TODO if both node and forget are in remove, this edge will be added twice
							if graph.edge(node, forget) {
								nice_decomposition.push((parent, Edge(node, forget)));
								parent += 1;
							} else if graph.edge(forget, node) {
								nice_decomposition.push((parent, Edge(forget, node)));
								parent += 1;
							}
						}
					}
				}

				// next work item is whatever follows from child or final leaf node, if child has no children
				if children[child].len() == 0 {
					work_queue.push_back(Work::Empty(parent, child))
				} else if children[child].len() > 1 {
					work_queue.push_back(Work::Join(parent, &children[child]));
				} else {
					work_queue.push_back(Work::Stretch(parent, children[child][0]));
				}
			}
			Work::Empty(mut parent, leaf_bag) => {
				// introduce everything to start with empty bag
				for &introduce in &td[leaf_bag].1 {
					nice_decomposition.push((parent, Introduce(introduce)));
					parent = nice_decomposition.len() - 1;
				}
				// add empty bag as leaf
				nice_decomposition.push((parent, Leaf));
			}
		}
	}

	nice_decomposition
}

fn reverse<T>(tree: &Vec<(usize, T)>) -> (usize, Vec<Vec<usize>>) {
	let (root, _)    = tree.iter().enumerate().find(|(i, (p, _))| p == i).unwrap();
	let mut children = vec![Vec::with_capacity(2); tree.len()];
	for (i, &(parent, _)) in tree.iter().enumerate() {
		// root should not be its own child
		if parent != i {
			children[parent].push(i);
		}
	}

	(root, children)
}

fn postorder<T>(tree: &Vec<(usize, T)>) -> Vec<usize> {
	let (root, children)   = reverse(&tree);
	let mut traverse_stack = vec![root];
	let mut traversal      = Vec::with_capacity(tree.len());

	// do a preorder
	while let Some(node) = traverse_stack.pop() {
		traversal.push(node);
		for &child in &children[node] {
			traverse_stack.push(child);
		}
	}

	// postorder is reversed preorder (with the exception of going right to left now)
	traversal.reverse();
	traversal
}

fn tree_index(tree: &NiceDecomposition, k: usize, size: usize) -> Vec<usize> {
	let (root, children) = reverse(tree);
	let mut index        = vec![0; size];
	let mut free         = vec![(0..k).collect_vec()];
	let mut work_stack   = vec![root];
	while let Some(node) = work_stack.pop() {
		match tree[node].1 {
			Forget(node) => {
				// claim first free index in current free list
				let free_index = free.last_mut().unwrap().pop().unwrap();
				index[node] = free_index;
			},
			Introduce(node) => {
				// free own index again
				free.last_mut().unwrap().push(index[node]);
			},
			Join => {
				// we need to be able to undo all changes to the free list if we jump into the right sub-tree
				free.push(free.last().unwrap().clone());
			},
			Leaf => {
				// we are done with this path, so dispose all changes done to the free list since last join
				free.pop();
			},
			// the rest is uninteresting
			_ => {}
		}
		// traverse in preorder
		for &child in &children[node] {
			work_stack.push(child);
		}
	}
	
	index
}

fn set_bit(bitmap: &mut usize, bit: usize, value: bool) {
	if value {
		*bitmap |= 1 << bit;
	} else {
		*bitmap &= !(1 << bit);
	}
}

fn get_bit(bitmap: &usize, bit: usize) -> bool {
	(bitmap & (1 << bit)) != 0
}
