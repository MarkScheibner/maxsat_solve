use std::collections::VecDeque;
use std::ops::Rem;

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

					// list vars of clause that are still free
					let literals = formula.clause(clause);
					let mut vars = literals.iter().map(|l| l.abs() as usize - 1).collect_vec();
					vars.retain(|v| free[*v]);
					// list clauses that share a free variable with clause
					let clauses  = vars.iter().flat_map(|v| &occurences[*v]).unique().collect_vec();

					// split configurations into those where clause is already satisfied and those where its not
					let (sat, unsat): (Vec<_>, Vec<_>) = configs.into_iter()
					                                            .partition(|(a, _, _)| get_bit(a, clause_bit));

					// list those variables, which have to be set to 1 in order to not satisfy clause
					let nonsat_assignment: Set<_> = literals.iter().filter(|l| **l < 0)
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
					for &&c in nonsat_clauses {
						set_bit(&mut nonsat_bitmask, tree_index[c], true);
					}
					// build configs where clause is not satisfied
					let nonsat_configs = unsat.into_iter().map(|(a, s, mut v)| {
						let new_assignment = a | nonsat_bitmask;
						v.extend(nonsat_assignment.clone());
						(new_assignment, s, v)
					});
					let sat_configs   = {
						// configs, where clause is already satisfied and will not be satisfied by any of vars
						let already_sat = sat.into_iter().map(|(a, s, mut v)| {
							let new_assignment = a | nonsat_bitmask;
							v.extend(nonsat_assignment.clone());
							(new_assignment, s, v)
						});
						// configs, where clause becomes satisfied (even if it already is) by one of vars
						let newly_sat = {
							// map vars into 0..|vars|
							let var_index: Map<_, _> = vars.iter().enumerate().map(|(i, v)| (*v, i)).collect();
							// build occurence list for vars. (negative clauses, positive clauses)
							let mut occurence_list   = vec![(Set::<usize>::default(), Set::<usize>::default()); vars.len()];
							for &&c in clauses.iter() {
								for &l in formula.clause(&c) {
									let var   = l.abs() as usize - 1;
									let index = var_index[&var];
									if l < 0 {
										occurence_list[index].0.insert(c);
									} else {
										occurence_list[index].1.insert(c);
									}
								}
							}

							for v in vars.iter() {
								let mut bitmask = 1 << clause_bit;
								// list clauses that agree with clause on v
								let satisfied_clauses = if nonsat_assignment.contains(&v) {
									// since not satisfying clause requires v to be 1, we set it to 0 to satisfy clause
									&occurence_list[var_index[v]].0
								} else {
									&occurence_list[var_index[v]].1
								};
								for c in satisfied_clauses.clone() {
									set_bit(&mut bitmask, tree_index[c], true);
									for l in formula.clause(&c) {
										// TODO use a var set
										let var = l.abs() as usize - 1;
										if !vars.contains(&var) { continue; }
										// remove clause from occurence list, as it is satisfied
										occurence_list[var_index[&var]].0.remove(&var);
										occurence_list[var_index[&var]].1.remove(&var);
									}
								}

								// TODO eliminate pure variables
								// TODO start going down tree



							}

							vec![]
						};

						// TODO configs where clause becomes satisfied
						already_sat.into_iter().chain(newly_sat.into_iter()).collect_vec()
					};

					// merge configs
					let mut configs = nonsat_configs.into_iter().chain(sat_configs.into_iter()).collect_vec();

					// forget clause
					// remove any config where clause is not satisfied if it's a hard clause
					if formula.is_hard(clause) {
						configs.retain(|(a, _, _)| get_bit(a, clause_bit));
					}
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

		Some((vec![true; self.size()], 0))
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
