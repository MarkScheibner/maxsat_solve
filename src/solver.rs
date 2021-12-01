use std::collections::VecDeque;

use itertools::Itertools;

use crate::graph::*;
use crate::fasttw::Decomposition;

type Assignment = Vec<bool>;
type NiceDecomposition = Vec<(usize, Node)>;
// assignment, score, fingerprint
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
use crate::solver::Node::*;

pub trait Solve {
	fn solve(self, td: Decomposition, k: usize) -> Option<(Assignment, usize)>;
}

impl Solve for Primal {
	fn solve(self, _td: Decomposition, k: usize) -> Option<(Assignment, usize)> {
		Some((vec![true; self.size()], 0))
	}
}
impl Solve for Dual {
	fn solve(self, _td: Decomposition, k: usize) -> Option<(Assignment, usize)> {
		Some((vec![true; self.size()], 0))
	}
}
impl Solve for Incidence {
	fn solve(self, td: Decomposition, k: usize) -> Option<(Assignment, usize)> {
		let nice_td = make_nice(&self, td);
		
		let tree_index       = tree_index(&nice_td, k);
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
					reject_unfulfilled(&mut config, clause, &tree_index, &self);

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
		let last           = &last.0[0];
		let score          = last.1;
		let variables      = last.2.iter().map(|v| v - self.num_clauses).sorted().collect::<Vec<_>>();
		let mut assignment = vec![false; self.size() - self.num_clauses];
		for &v in &variables {
			assignment[v] = true;
		}
		println!("c score: {}", score);
		println!("c true variables: {:?}", variables.iter().map(|v| v+1).collect::<Vec<_>>());
		println!("c num of true variables: {}", variables.len());
		println!("c assignment: {:?}", &assignment);
		let test = self.unfulfilled_clauses(&assignment);
		println!("c test result: {:?}", &test);
		println!("c len of test result: {:?}", test.len());
		Some((assignment, score))
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
fn reject_unfulfilled(config: &mut Vec<Configuration>, clause: usize, tree_index: &Vec<usize>, graph: &Incidence) {
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
	let  max_fingerprint = left.iter().map(|(a, _, _)| a).max().unwrap();
	let  mut indexes     = vec![0; max_fingerprint+1];
	for (i, (a, _ , _)) in left.iter().enumerate() {
		// we only care about assignment of variables here. this should still be a unique fingerprint
		let variable_assignment = a & !clauses;
		indexes[variable_assignment] = i+1
	}
	// keep only those variable assignments that are in left and in right
	right.into_iter().filter_map(|(a, s, v)| {
		let variable_assignment = a & !clauses;
		if variable_assignment > *max_fingerprint || indexes[variable_assignment] == 0 {
			None
		} else {
			// we can OR the assignments, since they only differ for the clauses
			// we can add the scores, since the shared clauses have not yet contributed their weight
			let  other_index                = indexes[variable_assignment] - 1;
			let (other_a, other_s, other_v) = &left[other_index];
			Some((a | other_a, s + other_s, v.iter().chain(other_v.iter()).unique().copied().collect()))
		}
	}).collect()
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
