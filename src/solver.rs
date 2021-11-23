use std::collections::VecDeque;

use itertools::Itertools;
use num::pow;

use crate::graph::*;
use crate::fasttw::Decomposition;

type Assignment = Vec<bool>;
type NiceDecomposition = Vec<(usize, Node)>;
// assignment, score, fingerprint
type Configuration = (Vec<bool>, usize, usize);

#[derive(Clone, Copy)]
enum Node {
	Leaf,
	Introduce(usize),
	Forget(usize),
	Edge(usize, usize),
	Join
}
use crate::solver::Node::*;

pub trait Solve {
	fn solve(self, td: Decomposition, k: usize) -> Option<Assignment>;
}

impl Solve for Primal {
	fn solve(self, _td: Decomposition, k: usize) -> Option<Assignment> {
		Some(vec![true; self.size()])
	}
}
impl Solve for Dual {
	fn solve(self, _td: Decomposition, k: usize) -> Option<Assignment> {
		Some(vec![true; self.size()])
	}
}
impl Solve for Incidence {
	fn solve(self, td: Decomposition, k: usize) -> Option<Assignment> {
		let nice_td = make_nice(&self, td);
		
		let tree_index       = tree_index(&nice_td, k);
		let traversal        = postorder(&nice_td);
		let mut config_stack = Vec::<Vec<Configuration>>::new();
		let traversal_len    = traversal.len();
		for (step, i) in traversal.into_iter().enumerate() {
			let (_, node) = &nice_td[i];
			match node {
				&Leaf => {
					// push first empty configuration
					config_stack.push(vec![(vec![false; k], 0, 0)]);
				},
				&Introduce(clause) if self.is_clause(clause) => {
					// do nothing...
				},
				&Introduce(var) => {
					let mut config = config_stack.pop().unwrap();
					let mut copies = Vec::with_capacity(config.len());
					// duplicate each assignment and set var to true and false
					for (a, s, f) in &mut config {
						let mut copy = a.clone();
						copy[tree_index[var]] = true;
						let new_fingerprint = *f | (1 << tree_index[var]);
						copies.push((copy, *s, new_fingerprint));
					}
					for copy in copies {
						config.push(copy);
					}

					config_stack.push(config);
				},
				&Forget(clause) if self.is_clause(clause) => {
					let mut config = config_stack.pop().unwrap();
					let mut reject = Vec::new();
					for (i, (a, s, f)) in config.iter_mut().enumerate() {
						if !a[tree_index[clause]] && self.is_hard(clause) {
							// clause is not true, "reject"
							reject.push(i);
						} else {
							// reset the bit for clause to false, update fingerprint and score accordingly
							a[tree_index[clause]] = false;
							*f &= !(1 << tree_index[clause]);
							*s += if self.is_hard(clause) { 0 } else { self.weight(clause) };
						}
					}
					// remove rejected configs
					reject.reverse();
					for i in reject {
						config.swap_remove(i);
					}

					config_stack.push(config);
				},
				&Forget(var) => {
					let mut config = config_stack.pop().unwrap();
					for (a, _, f) in &mut config {
						if a[tree_index[var]] {
							// update fingerprint if setting var to false changes assignment
							*f &= !(1 << tree_index[var]);
						}
						a[tree_index[var]] = false;
					}

					let max_fingerprint = config.iter().map(|c| c.2).max().unwrap();
					// we should save every byte possible here, so we also use usize instead of Option<usize>
					// for this we use 0 as None and i+1 as Some(i)
					let mut values      = vec![0; max_fingerprint+1];
					for (i, &(_, s, f)) in config.iter().enumerate() {
						match values[f] {
							// None
							0 => {
								values[f] = i+1;
							},
							// Some(i+1)
							some_i => {
								// TODO the rust compiler complains about not knowing the type of config[some_i].1 by
								// itself, so we have to get the score of other in this roundabout way
								let other: &(Vec<bool>, usize, usize) = &config[some_i-1];
								let other_s = other.1;
								if other_s < s {
									// this one is better
									values[f] = i+1;
								}
							}
						}
					}

					// deduplicate
					for i in (0..config.len()).rev() {
						let fingerprint = config[i].2;
						if values[fingerprint] != i+1 {
							// if an assignment does not find its own index, another assignment with the same
							// fingerprint had a better score, so we can remove this assigmnent
							config.swap_remove(i);
						}
					}

					config_stack.push(config);
				},
				&Edge(u, v)  => {
					let mut config = config_stack.pop().unwrap();
					let clause     = if u < v { u } else { v };
					let var        = if u < v { v } else { u };
					let negated    = var == u;
					let var_name   = var - self.num_clauses + 1;
					let clause_name= clause + 2;

					for (a, _, f) in &mut config {
						// evaluate literal based on assignment of var
						let literal_val = if negated { !a[tree_index[var]] } else { a[tree_index[var]] };
						// toggle the clause if the literal sets it to true
						if !a[tree_index[clause]] && literal_val {
							a[tree_index[clause]] = true;
							*f |= 1 << tree_index[clause];
						}
					}

					config_stack.push(config);
				},
				&Join => {
					let left_configs  = config_stack.pop().unwrap();
					let right_configs = config_stack.pop().unwrap();
					let mut values    = vec![None; pow(2, k)];
					for (_, s, f) in left_configs {
						values[f] = Some(s)
					}
					// keep only those assignments that are in left and in right
					let intersection = right_configs.into_iter().filter_map(|(a, s, f)| {
						// we can just add the scpres, since the shared clauses have not yet added their weight
						values[f].map(|other_s| (a, s + other_s, f))
					}).collect_vec();
					config_stack.push(intersection);
				}
			}

			if config_stack.last().map_or(true, |c| c.is_empty()) {
				println!("No solution found after {}/{} steps", step, traversal_len);
				return None;
			}
		}
		
		println!("{:?}", config_stack);
		Some(vec![true; self.size()])
	}
}

fn make_nice(graph: &impl Graph, td: Decomposition) -> NiceDecomposition {
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

fn tree_index(tree: &NiceDecomposition, k: usize) -> Vec<usize> {
	let (root, children) = reverse(tree);
	let mut index        = vec![0; tree.len()];
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
