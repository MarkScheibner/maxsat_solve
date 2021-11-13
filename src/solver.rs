use std::collections::VecDeque;

use itertools::Itertools;

use crate::graph::*;
use crate::fasttw::Decomposition;

type Assignment = Vec<bool>;
type NiceDecomposition = Vec<(usize, Node)>;
type Configuration = (Vec<Option<bool>>, usize);

enum Node {
	Leaf,
	Introduce(usize),
	Forget(usize),
	Edge(usize, usize),
	Join
}
use crate::solver::Node::*;

pub trait Solve {
	fn solve(self, td: Decomposition) -> Option<Assignment>;
}

impl Solve for Primal {
	fn solve(self, _td: Decomposition) -> Option<Assignment> {
		Some(vec![true; self.size()])
	}
}
impl Solve for Dual {
	fn solve(self, _td: Decomposition) -> Option<Assignment> {
		Some(vec![true; self.size()])
	}
}
impl Solve for Incidence {
	fn solve(self, td: Decomposition) -> Option<Assignment> {
		let nice_td = make_nice(&self, td);

		let tree_index       = tree_index(&nice_td);
		let traversal        = postorder(&nice_td);
		let mut config_stack = Vec::<Vec<Configuration>>::new();
		for i in traversal {
			let (parent, node) = &nice_td[i];
			match node {
				&Leaf => {
					config_stack.push(Vec::new())
				},
				&Introduce(node) => {},
				&Forget(node) => {
					if node < self.num_clauses {
						// node is clause
						let mut config = config_stack.pop().unwrap();
						// TODO remove config entry if clause is not true

						config_stack.push(config);
					}
				},
				&Edge(u, v) => {},
				&Join => {
					let left_configs  = config_stack.pop().unwrap();
					let right_configs = config_stack.pop().unwrap();
					// TODO join configs
					let joined = left_configs;
					config_stack.push(joined);
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

	while let Some((visited, node)) = traverse_stack.pop() {
		if visited {
			// were moving back up the tree
			traversal.push(node);
		} else {
			// were still moving down the tree. push the root as visited and the children as not visited
			traverse_stack.push((true, node));
			for &child in &children[node] {
				traverse_stack.push((false, child));
			}
		}
	}

	traversal
}
fn tree_index<T>(tree: &Vec<(usize, T)>) -> Vec<usize> {
	// TODO
	Vec::new()
}
