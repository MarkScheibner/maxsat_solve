use crate::parser::Formula;
use metrohash::MetroHashSet;
use std::iter::FromIterator;
use std::iter::Iterator;
use union_find::*;

type Edge = (usize, usize);
type WeightedClauseSet = (usize, MetroHashSet<isize>);

pub trait Graph {
	fn edge(&self, node1: usize, node2: usize) -> bool;
	fn list_edges(&self)                       -> Vec<Edge>;
	fn neighborhood(&self, node: usize)        -> MetroHashSet<usize>;
	fn degree(&self, node: usize)              -> usize;
	fn size(&self)                             -> usize;
	fn edge_count(&self)                       -> usize;
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

#[derive(Debug)]
pub struct PrimalGraph {
	size:       usize,
	_clauses:   Vec<WeightedClauseSet>,
	edges:      Vec<MetroHashSet<usize>>,
	edge_count: usize
}
impl Graph for PrimalGraph {
	fn edge(&self, u: usize, v: usize) -> bool {
		// an edge exists if one of the two nodes is contained in the adjacency set of the other
		self.edges[u].contains(&v) || self.edges[v].contains(&u)
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
impl From<Formula> for PrimalGraph {
	fn from(f: Formula) -> Self {
		// variables are nodes. nodes are joined by an edge if the respective variables appear in the same clause
		let mut clauses    = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges      = vec![MetroHashSet::default(); f.get_parameters().n_vars];
		let mut edge_count = 0;

		// add edges between variables of each clause
		for (weight, vars) in f.get_clauses() {
			// add clause to not lose information
			clauses.push((*weight, MetroHashSet::from_iter(vars.clone().into_iter())));
			// connect all variables of the clause to each other
			for var_a in vars {
				// variables start at 1
				let var_a = var_a.abs() as usize -1;
				for var_b in vars {
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

		PrimalGraph{
			size: f.get_parameters().n_vars,
			_clauses: clauses,
			edges,
			edge_count
		}
	}
}

#[derive(Debug)]
pub struct DualGraph {
	size:       usize,
	_clauses:   Vec<WeightedClauseSet>,
	edges:      Vec<MetroHashSet<usize>>,
	edge_count: usize
}
impl Graph for DualGraph {
	fn edge(&self, u: usize, v: usize) -> bool {
		// an edge exists if one of the two nodes is contained in the adjacency set of the other
		self.edges[u].contains(&v) || self.edges[v].contains(&u)
	}

	fn list_edges(&self) -> Vec<Edge> {
		// build edges from each neighborhood set
		let edge_iter = self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten();
		// only list edges in one direction
		edge_iter.filter(|(a, b)| a < b).collect()
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
impl From<Formula> for DualGraph {
	fn from(f: Formula) -> Self {
		// clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		let mut clauses    = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges      = vec![MetroHashSet::default(); f.get_parameters().n_clauses];
		let mut edge_count = 0;

		// we need to keep track of which clauses a variable is part of
		let mut var_sets: Vec<MetroHashSet<usize>> = vec![MetroHashSet::default(); f.get_parameters().n_vars];
		
		for (i, (weight, vars)) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((*weight, MetroHashSet::from_iter(vars.clone().into_iter())));
			
			for var in vars {
				// variables start at 1
				let var = var.abs() as usize - 1 ;
				// connect clause to all clauses that we already know contain var
				for clause in &var_sets[var] {
					edge_count += 1;
					edges[i].insert(*clause);
					edges[*clause].insert(i);
				}
				// add clause to set of clauses containing var
				var_sets[var].insert(i);
			}
		}

		DualGraph{
			size: f.get_parameters().n_clauses,
			_clauses: clauses,
			edges,
			edge_count
		}
	}
}

#[derive(Debug)]
pub struct IncidenceGraph {
	size:        usize,
	edges:       Vec<MetroHashSet<usize>>,
	num_clauses: usize,
	_clauses:    Vec<WeightedClauseSet>,
	edge_count:  usize
}
impl Graph for IncidenceGraph {
	fn edge(&self, u: usize, v: usize) -> bool {
		self.edges[u].contains(&v) || self.edges[v].contains(&u)
		
	}

	fn list_edges(&self) -> Vec<Edge> {
		// since there are only edges between a clause and a node, we only need the neighborhood of clauses
		self.edges.iter().take(self.num_clauses)
		                 .enumerate()
		                 .map(|(i, vars)| vars.iter().map(move |v| (i, *v)))
		                 .flatten().collect()
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
impl From<Formula> for IncidenceGraph {
	fn from(f: Formula) -> Self {
		let num_clauses    = f.get_parameters().n_clauses;
		let size           = num_clauses + f.get_parameters().n_vars;
		let mut edges      = vec![MetroHashSet::default(); size];
		let mut clauses    = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edge_count = 0;

		for (i, (weight, vars)) in f.get_clauses().iter().enumerate() {
			clauses.push((*weight, MetroHashSet::from_iter(vars.clone().into_iter())));
			let var_nodes = vars.iter().map(|i| i.abs() as usize + num_clauses - 1);
			// insert variables into neighborhood of clause and clause into neighborhood of variables
			var_nodes.for_each(|v| { edges[i].insert(v); edges[v].insert(i); edge_count += 1; });
		}

		IncidenceGraph {
			size,
			edges,
			num_clauses,
			_clauses: clauses,
			edge_count
		}
	}
}