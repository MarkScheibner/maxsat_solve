use crate::parser::Formula;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::iter::Iterator;

type Edge<T> = (T, T);
type WeightedClauseSet = (usize, HashSet<isize>);

pub trait Graph<T> {
	fn edge(&self, node1: &T, node2: &T) -> bool;
	fn from_formula(f: Formula) -> Self;
	fn list_edges(&self) -> Vec<Edge<T>>;
	fn neighborhood(&self, node: &T) -> HashSet<T>;
}

pub struct PrimalGraph {
	_clauses: Vec<WeightedClauseSet>,
	edges: Vec<HashSet<usize>>
}
impl Graph<usize> for PrimalGraph {
	fn edge(&self, node1: &usize, node2: &usize) -> bool {
		// an edge exists if one of the two nodes is contained in the adjacency set of the other
		self.edges[*node1 as usize].contains(node2) || self.edges[*node2 as usize].contains(node1)
	}

	fn from_formula(f: Formula) -> Self {
		// variables are nodes. nodes are joined by an edge if the respective variables appear in the same clause
		let mut clauses: Vec<WeightedClauseSet> = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges = Vec::with_capacity(f.get_parameters().n_vars);
		for _ in 0..f.get_parameters().n_vars {
			edges.push(HashSet::with_capacity(f.get_parameters().n_vars));
		}
		
		// add edges between variables of each clause
		for (weight, vars) in f.get_clauses() {
			// add clause to not lose information
			clauses.push((*weight, HashSet::from_iter(vars.clone().into_iter())));
			// connect all variables of the clause to each other
			for var_a in vars {
				let var_a = var_a.abs() as usize;
				for var_b in vars {
					let var_b = var_b.abs() as usize;
					if var_a != var_b {
						// variables start at 1
						edges[var_a as usize - 1].insert(var_b);
						edges[var_b as usize - 1].insert(var_a);
					}
				}
			}
		}

		PrimalGraph{
			_clauses: clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<usize>> {
		self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten().collect()
	}

	fn neighborhood(&self, node: &usize) -> HashSet<usize> {
		self.edges[*node].clone()
	}
}

pub struct DualGraph {
	_clauses: Vec<WeightedClauseSet>,
	edges: Vec<HashSet<usize>>
}
impl Graph<usize> for DualGraph {
	fn edge(&self, node1: &usize, node2: &usize) -> bool {
		self.edges[*node1].contains(node2) || self.edges[*node2].contains(node1)
	}

	fn from_formula(f: Formula) -> Self {
		// clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		
		let mut clauses = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges: Vec<HashSet<usize>> = Vec::with_capacity(f.get_parameters().n_clauses);
		for _ in 0..f.get_parameters().n_clauses {
			edges.push(HashSet::with_capacity(f.get_parameters().n_clauses));
		}

		// we need to keep track of which clauses a variable is part of
		let mut var_sets : Vec<HashSet<usize>> = Vec::with_capacity(f.get_parameters().n_vars);
		for _ in 0..f.get_parameters().n_vars {
			var_sets.push(HashSet::with_capacity(f.get_parameters().n_clauses));
		}
		
		for (i, (weight, vars)) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((*weight, HashSet::from_iter(vars.clone().into_iter())));
			
			for var in vars {
				// variables start at 1
				let var = var.abs() as usize - 1 ;
				// connect clause to all clauses that we already know contain var
				for clause in &var_sets[var] {
					edges[*clause].insert(i);
					edges[i].insert(*clause);
				}
				// add clause to set of clauses containing var
				var_sets[var as usize].insert(i);
			}
		}

		DualGraph{
			_clauses: clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<usize>> {
		self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i, *v))).flatten().collect()
	}

	fn neighborhood(&self, node: &usize) -> HashSet<usize> {
		self.edges[*node].clone()
	}
}

#[derive(Eq, PartialEq, Hash, Clone, Copy)]
pub enum IncidenceGraphNode {
	Clause(usize),
	Variable(usize)
}
pub struct IncidenceGraph {
	edges: Vec<HashSet<usize>>,
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
		let mut edges: Vec<HashSet<usize>> = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut weights: Vec<usize> = Vec::with_capacity(f.get_parameters().n_clauses);

		for (weight, vars) in f.get_clauses().iter() {
			let variables = vars.clone().into_iter().map(|i| i.abs() as usize);
			edges.push(HashSet::from_iter(variables));
			weights.push(*weight);
		}

		IncidenceGraph {
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

	fn neighborhood(&self, node: &IncidenceGraphNode) -> HashSet<IncidenceGraphNode> {
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
}