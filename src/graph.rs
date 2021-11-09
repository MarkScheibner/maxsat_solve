use crate::parser::Formula;
use metrohash::MetroHashSet;
use std::iter::FromIterator;
use std::iter::Iterator;
use union_find::*;
use ambassador::{delegatable_trait, Delegate};

type Edge = (usize, usize);
type IncidenceList = Vec<MetroHashSet<usize>>;
type WeightedClauseSet = (usize, MetroHashSet<isize>);

#[delegatable_trait]
pub trait Graph {
	fn edge(&self, node1: usize, node2: usize) -> bool;
	fn list_edges(&self)                       -> Vec<Edge>;
	fn neighborhood(&self, node: usize)        -> MetroHashSet<usize>;
	fn degree(&self, node: usize)              -> usize;
	fn size(&self)                             -> usize;
	fn edge_count(&self)                       -> usize;
}

#[derive(Debug)]
struct UndirectedGraph {
	size:       usize,
	edge_count: usize,
	edges:      IncidenceList
}
impl Graph for UndirectedGraph {
	fn edge(&self, u: usize, v: usize) -> bool {
		self.edges[u].contains(&v)
	}

	fn list_edges(&self) -> Vec<Edge> {
		// build edges from each neighborhood set
		let edge_iter = self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten();
		// only list edges in one direction
		edge_iter.filter(|(u, v)| u < v).collect()
	}

	fn neighborhood(&self, node: usize) -> MetroHashSet<usize> {
		self.edges[node].clone()
	}

	fn degree(&self, node: usize) -> usize {
		self.edges[node].len()
	}

	fn size(&self) -> usize {
		self.size
	}

	fn edge_count(&self) -> usize {
		self.edge_count
	}
}

#[derive(Debug)]
struct DirectedGraph {
	size:        usize,
	edge_count:  usize,
	successor:   IncidenceList,
	predecessor: IncidenceList
}
impl Graph for DirectedGraph {
	fn edge(&self, u: usize, v: usize) -> bool {
		// edges go only in one direction, so v has to be a successor to u
		self.successor[u].contains(&v)
	}

	fn list_edges(&self) -> Vec<Edge> {
		// edges go only form nodes to their successors
		self.successor.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten().collect()
	}

	fn neighborhood(&self, node: usize) -> MetroHashSet<usize> {
		// TODO this might take O(n), which is ok, as long as we iterate the whole neighborhood
		self.successor[node].union(&self.predecessor[node]).copied().collect()
	}

	fn degree(&self, node: usize) -> usize {
		self.successor[node].len() + self.predecessor[node].len()
	}

	fn size(&self) -> usize {
		self.size
	}

	fn edge_count(&self) -> usize {
		self.edge_count
	}
}

#[derive(Debug, Delegate)]
#[delegate(Graph, target="inner")]
pub struct Primal {
	inner:    UndirectedGraph,
	_clauses: Vec<WeightedClauseSet>
}
impl From<Formula> for Primal {
	fn from(f: Formula) -> Self {
		// variables are nodes. nodes are joined by an edge if the respective variables appear in the same clause
		let mut clauses    = Vec::with_capacity(f.n_clauses);
		let mut edges      = vec![MetroHashSet::default(); f.n_vars];
		let mut edge_count = 0;

		// add edges between variables of each clause
		for (i, clause) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((f.get_weights()[i], MetroHashSet::from_iter(clause.clone().into_iter())));
			// connect all variables of the clause to each other
			for var_a in clause {
				// variables start at 1
				let var_a = var_a.abs() as usize -1;
				for var_b in clause {
					let var_b = var_b.abs() as usize -1;
					// no edges to self
					if var_a != var_b {
						// variables start at 1
						edges[var_a].insert(var_b);
						edges[var_b].insert(var_a);
						edge_count += 1;
					}
				}
			}
		}

		Primal {
			inner: UndirectedGraph {
				size: f.n_vars,
				edge_count,
				edges
			},
			_clauses: clauses
		}
	}
}

#[derive(Debug, Delegate)]
#[delegate(Graph, target="inner")]
pub struct Dual {
	inner:    UndirectedGraph,
	_clauses: Vec<WeightedClauseSet>
}
impl From<Formula> for Dual {
	fn from(f: Formula) -> Self {
		// clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		let mut clauses    = Vec::with_capacity(f.n_clauses);
		let mut edges      = vec![MetroHashSet::default(); f.n_clauses];
		let mut edge_count = 0;

		// we need to keep track of which clauses a variable is part of
		let mut var_sets: Vec<MetroHashSet<usize>> = vec![MetroHashSet::default(); f.n_vars];
		
		for (i, clause) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((f.get_weights()[i], MetroHashSet::from_iter(clause.clone().into_iter())));
			
			for var in clause {
				// variables start at 1
				let var = var.abs() as usize - 1 ;
				// connect clause to all clauses that we already know contain var
				// TODO move this
				for clause in &var_sets[var] {
					edge_count += 1;
					edges[i].insert(*clause);
					edges[*clause].insert(i);
				}
				// add clause to set of clauses containing var
				var_sets[var].insert(i);
			}
		}

		Dual {
			inner: UndirectedGraph {
				size: f.n_clauses,
				edges,
				edge_count
			},
			_clauses: clauses
		}
	}
}

#[derive(Debug, Delegate)]
#[delegate(Graph, target="inner")]
pub struct Incidence {
	inner:    DirectedGraph,
	_clauses: Vec<WeightedClauseSet>
}
impl From<Formula> for Incidence {
	fn from(f: Formula) -> Self {
		let num_clauses     = f.n_clauses;
		let size            = num_clauses + f.n_vars;
		let mut predecessor = vec![MetroHashSet::default(); size];
		let mut successor   = vec![MetroHashSet::default(); size];
		let mut clauses     = Vec::with_capacity(f.n_clauses);
		let mut edge_count  = 0;

		for (c, clause) in f.get_clauses().iter().enumerate() {
			clauses.push((f.get_weights()[c], MetroHashSet::from_iter(clause.clone().into_iter())));
			// insert variables into neighborhood of clause and clause into neighborhood of variables
			for &var in clause {
				// the node of the variable
				let var_node = var.abs() as usize + num_clauses -1;
				// determine direction of edge
				if var < 0 {
					// positive literal: edge goes from clause to variable
					successor[c].insert(var_node);
					predecessor[var_node].insert(c);
				} else {
					// negative literal: edge goes from variable to clause
					successor[var_node].insert(c);
					predecessor[c].insert(var_node);
				}
				edge_count += 1;
			}
		}

		Incidence {
			inner: DirectedGraph {
				size,
				successor,
				predecessor,
				edge_count
			},
			_clauses: clauses
		}
	}
}

pub fn connected_components(graph: &impl Graph) -> Vec<Vec<usize>> {
	// find components with union find
	let mut components_uf: QuickUnionUf<UnionBySize> = UnionFind::new(graph.size());
	for u in 0..graph.size() {
		for v in graph.neighborhood(u) {
			components_uf.union(u, v);
		}
	}


	let mut components = vec![Vec::new(); graph.size()];
	for u in 0..graph.size() {
		components[components_uf.find(u)].push(u);
	}

	components.retain(|c| c.len() > 1);
	components
}