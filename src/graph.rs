use crate::parser::Formula;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::iter::Iterator;

type Edge<T> = (T, T);
type WeightedClauseSet = (u32, HashSet<i32>);

pub trait Graph<T> {
	fn edge(&self, node1: &T, node2: &T) -> bool;
	fn from_formula(f: Formula) -> Self;
	fn list_edges(&self) -> Vec<&Edge<T>>;
}

// TODO find a way to retain clause weight
pub struct PrimalGraph {
	clauses: Vec<WeightedClauseSet>,
	// TODO maybe use Vec<Vec<bool>>
	edges: Vec<HashSet<i32>>
}
impl Graph<i32> for PrimalGraph {
	fn edge(&self, node1: &i32, node2: &i32) -> bool {
		// TODO maybe need abs-values
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
			for var in vars {
				vars.iter().for_each(|i| {
					// no edges to self
					if i != var {
						edges[*var as usize].insert(*i);
					}
				});
			}
		}

		PrimalGraph{
			clauses,
			edges
		}
	}

	fn list_edges(&self) -> Vec<&Edge<i32>> {
		// TODO
		Vec::new()
	}
}

pub struct DualGraph {
	edges: Vec<HashSet<u32>>
}
impl Graph<u32> for DualGraph {
	fn edge(&self, node1: &u32, node2: &u32) -> bool {
		self.edges[*node1 as usize].contains(node2) || self.edges[*node2 as usize].contains(node1)
	}

	fn from_formula(f: Formula) -> Self {
		// TODO clauses are nodes. nodes are joined by an edge if the respective clauses share a variable
		
		let mut clauses: Vec<WeightedClauseSet> = Vec::with_capacity(f.get_parameters().n_clauses);
		
		let mut var_sets = Vec::with_capacity(f.get_parameters().n_vars);
		for _ in 0..f.get_parameters().n_vars {
			var_sets.push(HashSet::with_capacity(f.get_parameters().n_clauses));
		}
		
		// for each variable find the set of clauses that contains that variable
		for (i, (weight, vars)) in f.get_clauses().iter().enumerate() {
			// add clause to not lose information
			clauses.push((*weight, HashSet::from_iter(vars.clone().into_iter())));
			// add clause to set
			for var in vars {
				var_sets[var.abs() as usize].insert(i);
			}
		}

		// each variable that has more than one clause associated with it will conversely be a variable that is shared
		// by these clauses. thus, we can use those sets to find the edges
		for set in var_sets {
			for clause_a in &set {
				for clause_b in &set {
					if clause_a != clause_b {
						// TODO
					}
				}
			}
		}

		DualGraph{
			edges: Vec::new()
		}
	}

	fn list_edges(&self) -> Vec<&Edge<u32>> {
		// TODO
		Vec::new()
	}
}

// TODO this might not be needed
#[derive(Eq, PartialEq, Hash, Clone, Copy)]
enum IncidenceGraphNode {
	Clause(u32, u32),
	Variable(i32)
}
pub struct IncidenceGraph {
	edges: Vec<HashSet<i32>>,
	clause_weights: Vec<u32>
}
impl Graph<IncidenceGraphNode> for IncidenceGraph {
	fn edge(&self, node1: &IncidenceGraphNode, node2: &IncidenceGraphNode) -> bool {
		use IncidenceGraphNode::*;

		match (node1, node2) {
			// only clauses and variables are connected
			(Clause(_, a), Variable(b)) |
			(Variable(b), Clause(_, a))   => self.edges[*a as usize].contains(b),
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
			clause_weights: weights
		}
	}

	fn list_edges(&self) -> Vec<&Edge<IncidenceGraphNode>> {
		use IncidenceGraphNode::*;
		let clause_list_iter = self.clause_weights.iter().zip(self.edges.iter());
		// TODO the edges cant be borrowed here
		let _ : Vec<_> = clause_list_iter.enumerate()
		         .map(|(i, (w, vars))| vars.iter().map(move |v| (Clause(*w, i as u32), Variable(*v))))
		         .flatten().collect();
		Vec::new()
	}
}