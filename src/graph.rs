use crate::parser::Formula;
use metrohash::MetroHashSet;
use std::iter::FromIterator;
use std::iter::Iterator;

type Edge<T> = (T, T);
type WeightedClauseSet = (usize, MetroHashSet<isize>);

pub trait Graph<T> {
	fn edge(&self, node1: &T, node2: &T) -> bool;
	fn from_formula(f: Formula)          -> Self;
	fn list_edges(&self)                 -> Vec<Edge<T>>;
	fn neighborhood(&self, node: &T)     -> MetroHashSet<T>;
	fn size(&self)                       -> usize;
}

#[derive(Debug)]
pub struct PrimalGraph {
	size:     usize,
	_clauses: Vec<WeightedClauseSet>,
	edges:    Vec<MetroHashSet<usize>>
}
impl Graph<usize> for PrimalGraph {
	fn edge(&self, node_a: &usize, node_b: &usize) -> bool {
		let a_to_b = self.edges[*node_a].contains(node_b);
		let b_to_a = self.edges[*node_b].contains(node_a);
		// an edge exists if one of the two nodes is contained in the adjacency set of the other
		a_to_b || b_to_a
	}

	fn from_formula(f: Formula) -> Self {
		// variables are nodes. nodes are joined by an edge if the respective variables appear in the same clause
		let mut clauses = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges   = vec![MetroHashSet::default(); f.get_parameters().n_vars];
		
		// add edges between variables of each clause
		for (weight, vars) in f.get_clauses() {
			// add clause to not lose information
			clauses.push((*weight, MetroHashSet::from_iter(vars.clone().into_iter())));
			// connect all variables of the clause to each other
			for var_a in vars {
				let var_a = var_a.abs() as usize;
				for var_b in vars {
					let var_b = var_b.abs() as usize;
					// no edges to self
					if var_a != var_b {
						// variables start at 1
						edges[var_a - 1].insert(var_b);
						edges[var_b - 1].insert(var_a);
					}
				}
			}
		}

		PrimalGraph{
			size: f.get_parameters().n_vars,
			_clauses: clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<usize>> {
		// build edges from each neighborhood set
		let edge_iter = self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i+1, *v))).flatten();
		// only list edges in one direction
		edge_iter.filter(|(a, b)| a < b).collect()
	}

	fn neighborhood(&self, node: &usize) -> MetroHashSet<usize> {
		self.edges[*node].clone()
	}

	fn size(&self) -> usize {
		self.size
	}
}

#[derive(Debug)]
pub struct DualGraph {
	size: usize,
	_clauses: Vec<WeightedClauseSet>,
	edges: Vec<MetroHashSet<usize>>
}
impl Graph<usize> for DualGraph {
	fn edge(&self, node_a: &usize, node_b: &usize) -> bool {
		let a_to_b = self.edges[*node_a].contains(node_b);
		let b_to_a = self.edges[*node_b].contains(node_a);
		// an edge exists if one of the two nodes is contained in the adjacency set of the other
		a_to_b || b_to_a
	}

	fn from_formula(f: Formula) -> Self {
		// clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		let mut clauses = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges   = vec![MetroHashSet::default(); f.get_parameters().n_clauses];

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
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<usize>> {
		// build edges from each neighborhood set
		let edge_iter = self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten();
		// only list edges in one direction
		edge_iter.filter(|(a, b)| a < b).collect()
	}

	fn neighborhood(&self, node: &usize) -> MetroHashSet<usize> {
		self.edges[*node].clone()
	}

	fn size(&self) -> usize {
		self.size
	}
}

#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
pub enum IncidenceGraphNode {
	Clause(usize),
	Variable(usize)
}
#[derive(Debug)]
pub struct IncidenceGraph {
	size: usize,
	edges: Vec<MetroHashSet<usize>>,
	_clause_weights: Vec<usize>
}
impl Graph<IncidenceGraphNode> for IncidenceGraph {
	fn edge(&self, node1: &IncidenceGraphNode, node2: &IncidenceGraphNode) -> bool {
		use IncidenceGraphNode::*;

		match (node1, node2) {
			// only clauses and variables are connected
			(Clause(a), Variable(b)) |
			(Variable(b), Clause(a))   => self.edges[*a as usize].contains(b),
			// there are no clause -> clause or variable -> variable edges
			_ => false
		}
	}

	fn from_formula(f: Formula) -> Self {
		let mut edges   = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut weights = Vec::with_capacity(f.get_parameters().n_clauses);

		for (weight, vars) in f.get_clauses().iter() {
			let variables = vars.clone().into_iter().map(|i| i.abs() as usize);
			edges.push(MetroHashSet::from_iter(variables));
			weights.push(*weight);
		}

		IncidenceGraph {
			size: f.get_parameters().n_clauses + f.get_parameters().n_vars,
			edges,
			_clause_weights: weights
		}
	}

	fn list_edges(&self) -> Vec<Edge<IncidenceGraphNode>> {
		use IncidenceGraphNode::*;
		self.edges.iter().enumerate()
		                 .map(|(i, vars)| vars.iter().map(move |v| (Clause(i), Variable(*v))))
		                 .flatten().collect()
	}

	fn neighborhood(&self, node: &IncidenceGraphNode) -> MetroHashSet<IncidenceGraphNode> {
		use IncidenceGraphNode::*;
		match node {
			Clause(c) => self.edges[*c].iter().map(|i| Variable(*i)).collect(),
			// TODO this takes O(m)
			Variable(v) => {
				self.edges.iter().enumerate().filter_map(|(i, s)| {
					if s.contains(v) {
						Some(Clause(i))
					} else {
						None
					}
				}).collect()
			}
		}
	}

	fn size(&self) -> usize {
		self.size
	}
}