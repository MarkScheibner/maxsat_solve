use crate::parser::Formula;
use std::collections::HashSet;
use std::iter::FromIterator;

type WeightedClauseSet = (i32, HashSet<i32>);

pub trait Graph<T> {
	fn edge(&self, node1: T, node2: T) -> bool;
	fn from_formula(f: Formula) -> Self;
}

// TODO find a way to retain clause weight
pub struct PrimalGraph {
	size: u32,
	clauses: Vec<WeightedClauseSet>,
	edges: HashSet<(i32, i32)>
}
impl Graph<i32> for PrimalGraph {
	fn edge(&self, node1: i32, node2: i32) -> bool {
		self.edges.contains(&(node1, node2)) || self.edges.contains(&(node2, node1))
	}

	fn from_formula(f: Formula) -> Self {
		// TODO variables are nodes. nodes are joined by an edge if the respective variables appear in the same clause
		let mut clauses: Vec<WeightedClauseSet> = Vec::with_capacity(f.get_parameters().n_clauses);

		// TODO find a better way to estimate the amount of edges needed
		let set_capacity = f.get_parameters().n_vars * f.get_parameters().n_vars;
		let edges = HashSet::<(i32, i32)>::with_capacity(set_capacity);
		
		for (weight, vars) in f.get_clauses() {
			// add clause to not lose information
			clauses.push((*weight, HashSet::from_iter(vars.clone().into_iter())));
		}

		PrimalGraph{
			size: f.get_parameters().n_vars as u32,
			clauses,
			edges: HashSet::new()
		}
	}
}

pub struct DualGraph {
	size: u32,
	edges: HashSet<(i32, i32)>
}
impl Graph<i32> for DualGraph {
	fn edge(&self, node1: i32, node2: i32) -> bool {
		self.edges.contains(&(node1, node2)) || self.edges.contains(&(node2, node1))
	}

	fn from_formula(f: Formula) -> Self {
		// TODO clauses are nodes. nodes are joined by an edge if the respective clausesshare a variable

		DualGraph{
			size: f.get_parameters().n_clauses as u32,
			edges: HashSet::new()
		}
	}
}
#[derive(Eq, PartialEq, Hash)]
enum IncidenceGraphNode {
	Clause(u32),
	Variable(u32)
}
pub struct IncidenceGraph {
	size: u32,
	edges: HashSet<(IncidenceGraphNode, IncidenceGraphNode)>
}
impl Graph<IncidenceGraphNode> for IncidenceGraph {
	fn edge(&self, node1: IncidenceGraphNode, node2: IncidenceGraphNode) -> bool {
		// TODO
		self.edges.contains(&(node1, node2)) || self.edges.contains(&(node2, node1))
	}

	fn from_formula(f: Formula) -> Self {
		IncidenceGraph {
			size: 0,
			edges: HashSet::new()
		}
	}
}