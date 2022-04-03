use std::collections::VecDeque;
use itertools::Itertools;

pub use crate::graph::Graph;

pub use crate::fasttw::Decomposition;
pub use crate::parser::Formula;

pub type Assignment = Vec<bool>;
pub type NiceDecomposition = Vec<(usize, Node)>;
// assignment (bit-map), score, true variables
pub type Configuration = (usize, usize, Vec<usize>);

#[derive(Clone, Copy, Debug)]
pub enum Node {
	Leaf,
	Introduce(usize),
	Forget(usize),
	Edge(usize, usize),
	Join
}

pub use crate::solver::Node::*;

pub trait Solve {
	fn solve(self, td: Decomposition, k: usize, formula: Formula) -> Option<(Assignment, usize)>;
}


pub fn duplicate_configs(configs: &mut Vec<Configuration>, var: usize, tree_index: &Vec<usize>) {
	// clone configs and set bit for var to 1
	let clones = configs.iter().cloned().map(|(mut a, s, mut v)| {
		set_bit(&mut a, tree_index[var], true);
		v.push(var);

		(a, s, v)
	}).collect_vec();

	// append clones to config
	configs.extend(clones);
}

pub fn deduplicate(config: &mut Vec<Configuration>) {
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


pub fn make_nice(graph: &impl Graph, td: Decomposition, very_nice: bool) -> NiceDecomposition {
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

pub fn reverse<T>(tree: &Vec<(usize, T)>) -> (usize, Vec<Vec<usize>>) {
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

fn post_order<T>(tree: &Vec<(usize, T)>) -> Vec<usize> {
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

pub fn traverse_order(tree: &Vec<(usize, Node)>) -> Vec<usize> {
	// let mut optimized_subtrees = vec![];

	// for i in post_order(tree) {
	// 	let (_, node) = tree[i];
	// 	match node {
	// 		Leaf => {
	// 			optimized_subtrees.push((1, vec![i]))
	// 		},
	// 		Forget(_) | Introduce(_) | Edge(_, _) => {
	// 			let (stack_cost, mut traversal) = optimized_subtrees.pop().unwrap();
	// 			traversal.push(i);
	// 			optimized_subtrees.push((stack_cost, traversal));
	// 		},
	// 		Join => {
	// 			let (left_cost, left_traversal)   = optimized_subtrees.pop().unwrap();
	// 			let (right_cost, right_traversal) = optimized_subtrees.pop().unwrap();
	// 			if left_cost < right_cost {
	// 				// go right first to reduce its cost to 1
	// 				let mut traversal: Vec<_> = right_traversal.into_iter().chain(left_traversal.into_iter()).collect();
	// 				traversal.push(i);
	// 				optimized_subtrees.push((1 + left_cost, traversal));
	// 			} else {
	// 				// go left first to reduce its cost to 1
	// 				let mut traversal: Vec<_> = left_traversal.into_iter().chain(right_traversal.into_iter()).collect();
	// 				traversal.push(i);
	// 				optimized_subtrees.push((1 + right_cost, traversal));
	// 			}
	// 		}
	// 	}
	// }

	// optimized_subtrees.pop().unwrap().1
	post_order(tree)
}

pub fn tree_index(tree: &NiceDecomposition, k: usize, size: usize) -> Vec<usize> {
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

pub fn set_bit(bitmap: &mut usize, bit: usize, value: bool) {
	if value {
		*bitmap |= 1 << bit;
	} else {
		*bitmap &= !(1 << bit);
	}
}

pub fn get_bit(bitmap: &usize, bit: usize) -> bool {
	(bitmap & (1 << bit)) != 0
}
