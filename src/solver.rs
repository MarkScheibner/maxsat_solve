use std::collections::VecDeque;

use itertools::Itertools;
use num::pow;

use crate::graph::*;
use crate::fasttw::Decomposition;

type Assignment = Vec<bool>;
type NiceDecomposition = Vec<(usize, Node)>;
// values, weight, config-index
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
		for i in traversal {
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
					let mut config = config_stack.pop()?;
					let mut copies = Vec::with_capacity(pow(2, k-1));
					// duplicate each config and set var to true and false
					for (c, w, i) in &mut config {
						let mut copy = c.clone();
						copy[tree_index[var]] = true;
						let config_index = *i + pow(2, tree_index[var]);
						copies.push((copy, *w, config_index));
					}
					for copy in copies {
						config.push(copy);
					}

					config_stack.push(config);
				},
				&Forget(clause) if self.is_clause(clause) => {
					let mut config = config_stack.pop()?;
					let mut reject = Vec::new();
					for (i, (c, w, config_index)) in config.iter_mut().enumerate() {
						// this is awkward, but if-let cant be negated
						if !c[tree_index[clause]] {
							// clause is not true, "reject"
							reject.push(i);
						} else {
							// reset the bit for clause to false, update index and weight accordingly
							c[tree_index[clause]] = false;
							*config_index -= pow(2, tree_index[clause]);
							*w += if self.is_hard(clause) { 0 } else { self.weight(clause) };
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
					let mut config = config_stack.pop()?;
					for (c, _, i) in &mut config {
						if c[tree_index[var]] {
							// since we are going to set the var to false, if it is set to true we need to update i
							*i -= pow(2, tree_index[var]);
						}
						c[tree_index[var]] = false;
					}
					
					let mut values      = vec![None; pow(2, k)];
					let mut low_remove  = Vec::new();
					let mut high_remove = Vec::new();
					for (i, &(_, w, config_index)) in config.iter().enumerate() {
						match values[config_index] {
							Some((other_i, other_w)) => {
								if other_w > w {
									// other one is better
									high_remove.push(i)
								} else {
									// this one is better
									low_remove.push(other_i);
									values[config_index] = Some((i, w));
								}
							},
							None => {
								values[config_index] = Some((i, w));
							}
						}
					}

					// TODO we need low_remove to be sorted, but at this point we cannot guarantee that.
					for i in low_remove.into_iter().chain(high_remove.into_iter()).rev() {
						config.swap_remove(i);
					}

					config_stack.push(config);
				},
				&Edge(u, v)  => {
					let mut config  = config_stack.pop()?;
					let clause      = if u < v { u } else { v };
					let var         = if u < v { v } else { u };
					for (c, _, i) in &mut config {
						// evaluate literal based on variable assignment
						let literal_val = if u < v { c[tree_index[var]] } else { !c[tree_index[var]] };
						// toggle the clause if the literal sets it to true
						if !c[tree_index[clause]] && literal_val {
							c[tree_index[clause]] = true;
							*i += pow(2, tree_index[clause]);
						}
					}

					config_stack.push(config);
				},
				&Join => {
					let left_configs  = config_stack.pop()?;
					let right_configs = config_stack.pop()?;
					let mut values    = vec![None; pow(2, k)];
					for (_, w, i) in left_configs {
						values[i] = Some(w)
					}
					// keep only those configs that are in left and in right
					let intersection = right_configs.into_iter().filter_map(|(c, w, i)| {
						// we can just add the values, since the shared clauses have not yet added their weight
						values[i].map(|other_w| (c, w + other_w, i))
					}).collect_vec();
					config_stack.push(intersection);
				}
			}
		}

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

	if children[root].len() > 1 {
		work_queue.push_back(Work::Join(0, &children[root]));
	} else {
		work_queue.push_back(Work::Stretch(0, children[root][0]))
	}

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
			Work::Stretch(parent, child) => {
				// while we stretch from the parent to its child, we actually add and remove from the child
				let (parent_bag, src_bag) = &td[child];
				let dest_bag              = &td[*parent_bag].1;

				// find out which nodes to introduce (add) or forget (remove) if moving from src_bag to dest_bag
				let add    = dest_bag.into_iter().filter(|v| !src_bag.contains(v)).collect_vec();
				let remove = src_bag.into_iter().filter(|v| !dest_bag.contains(v)).collect_vec();

				let mut parent = parent;

				for &introduce in add {
					nice_decomposition.push((parent, Introduce(introduce)));
					parent = nice_decomposition.len() - 1;
				}
				for &forget in remove {
					nice_decomposition.push((parent, Forget(forget)));
					parent += 1;
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
	let mut traverse_stack = vec![(false, root)];
	let mut traversal      = Vec::with_capacity(tree.len());

	// while let Some((visited, node)) = traverse_stack.pop() {
	// 	if visited {
	// 		// were moving back up the tree
	// 		traversal.push(node);
	// 	} else {
	// 		// were still moving down the tree. push the root as visited and the children as not visited
	// 		traverse_stack.push((true, node));
	// 		for &child in &children[node] {
	// 			traverse_stack.push((false, child));
	// 		}
	// 	}
	// }
	while let Some((_, node)) = traverse_stack.pop() {
		traversal.push(node);
		for &child in &children[node] {
			traverse_stack.push((false, child));
		}
	}

	traversal.reverse();
	traversal
}

fn tree_index(tree: &NiceDecomposition, k: usize) -> Vec<usize> {
	let (root, children) = reverse(tree);
	let mut index        = vec![0; tree.len()];
	let mut free         = vec![(0..k-1).collect_vec()];
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
