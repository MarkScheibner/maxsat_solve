use std::collections::VecDeque;

use itertools::Itertools;

use crate::graph::*;
use crate::fasttw::Decomposition;

type Assignment = Vec<bool>;

enum Node {
	Leaf,
	Introduce(usize),
	Forget(usize),
	Edge(usize, usize),
	Join
}
use crate::solver::Node::*;

enum Work<'a> {
	// parent node, children
	Join(usize,  &'a [usize]),
	// parent node, child
	Stretch(usize, usize),
	// parent node, leaf-bag
	Empty(usize, usize)
}

struct NiceDecomposition {
	size: usize,
	tree: Vec<(usize, Node)>
}

pub fn solve(graph: &dyn Graph, td: Decomposition) -> Assignment {
	let _td = make_nice(graph, td);

	// TODO do cool stuff with nice decomposition

	Vec::new()
}

fn make_nice(graph: &dyn Graph, td: Decomposition) -> NiceDecomposition {
	let mut nice_decomposition = Vec::new();

	// top down is easier
	let (root, _)    = td.iter().enumerate().find(|(i, (p, _))| p == i).unwrap();
	let mut children = vec![Vec::new(); td.len()];
	for (i, &(parent, _)) in td.iter().enumerate() {
		// root should not be its own child
		if parent != i {
			children[parent].push(i);
		}
	}

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
							parent += 1
						} else if graph.edge(forget, node) {
							nice_decomposition.push((parent, Edge(forget, node)))
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

	NiceDecomposition {
		size: nice_decomposition.len(),
		tree: nice_decomposition
	}
}