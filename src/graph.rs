use crate::parser::Formula;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::iter::Iterator;

type Edge<T> = (T, T);
type WeightedClauseSet = (u32, HashSet<i32>);

pub trait Graph<T> {
	fn edge(&self, node1: &T, node2: &T) -> bool;
	fn from_formula(f: Formula) -> Self;
	fn list_edges(&self) -> Vec<Edge<T>>;
	fn neighborhood(&self, node: &T) -> HashSet<T>;
}

pub struct PrimalGraph {
	_clauses: Vec<WeightedClauseSet>,
	edges: Vec<HashSet<i32>>
}
impl Graph<i32> for PrimalGraph {
	fn edge(&self, node1: &i32, node2: &i32) -> bool {
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
				for var_b in vars {
					if var_a != var_b {
						edges[*var_a as usize].insert(*var_b);
						edges[*var_b as usize].insert(*var_a);
					}
				}
			}
		}

		PrimalGraph{
			_clauses: clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<i32>> {
		self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i as i32, *v))).flatten().collect()
	}

	fn neighborhood(&self, node: &i32) -> HashSet<i32> {
		self.edges[*node as usize].clone()
	}
}

pub struct DualGraph {
	_clauses: Vec<WeightedClauseSet>,
	edges: Vec<HashSet<u32>>
}
impl Graph<u32> for DualGraph {
	fn edge(&self, node1: &u32, node2: &u32) -> bool {
		self.edges[*node1 as usize].contains(node2) || self.edges[*node2 as usize].contains(node1)
	}

	fn from_formula(f: Formula) -> Self {
		// clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		
		let mut clauses: Vec<WeightedClauseSet> = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut edges : Vec<HashSet<u32>> = Vec::with_capacity(f.get_parameters().n_clauses);
		for _ in 0..f.get_parameters().n_clauses {
			edges.push(HashSet::with_capacity(f.get_parameters().n_clauses));
		}

		// we need to keep track of which clauses a variable is part of
		let mut var_sets : Vec<HashSet<u32>> = Vec::with_capacity(f.get_parameters().n_vars);
		for _ in 0..f.get_parameters().n_vars {
			var_sets.push(HashSet::with_capacity(f.get_parameters().n_clauses));
		}
		
		for (i, (weight, vars)) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((*weight, HashSet::from_iter(vars.clone().into_iter())));
			
			for var in vars {
				let var = var.abs();
				// connect clause to all clauses that we already know contain var
				for clause in &var_sets[var as usize] {
					edges[*clause as usize].insert(i as u32);
					edges[i as usize].insert(*clause);
				}
				// add clause to set of clauses containing var
				var_sets[var as usize].insert(i as u32);
			}
		}

		DualGraph{
			_clauses: clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<Edge<u32>> {
		self.edges.iter().enumerate().map(|(i, s)| s.iter().map(move |v| (i as u32, *v))).flatten().collect()
	}

	fn neighborhood(&self, node: &u32) -> HashSet<u32> {
		self.edges[*node as usize].clone()
	}
}

#[derive(Eq, PartialEq, Hash, Clone, Copy)]
pub enum IncidenceGraphNode {
	Clause(u32),
	Variable(i32)
}
pub struct IncidenceGraph {
	edges: Vec<HashSet<i32>>,
	_clause_weights: Vec<u32>
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
		let mut edges: Vec<HashSet<i32>> = Vec::with_capacity(f.get_parameters().n_clauses);
		let mut weights: Vec<u32> = Vec::with_capacity(f.get_parameters().n_clauses);

		for (weight, vars) in f.get_clauses().iter() {
			let variables = vars.clone().into_iter().map(|i| i.abs());
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
		                 .map(|(i, vars)| vars.iter().map(move |v| (Clause(i as u32), Variable(*v))))
		                 .flatten().collect()
	}

	fn neighborhood(&self, node: &IncidenceGraphNode) -> HashSet<IncidenceGraphNode> {
		use IncidenceGraphNode::*;
		match node {
			Clause(c) => self.edges[*c as usize].iter().map(|i| Variable(*i)).collect(),
			// TODO this takes O(m)
			Variable(v) => {
				self.edges.iter().enumerate().filter_map(|(i, s)| {
					if s.contains(v) {
						Some(Clause(i as u32))
					} else {
						None
					}
				}).collect()
			}
		}
	}
}