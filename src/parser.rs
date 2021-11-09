use std::cell::Cell;

use metrohash::MetroHashMap;
use itertools::Itertools;
use crate::graph::{Dual, connected_components};

type Clause = Vec<isize>;
type Renaming = MetroHashMap<usize, usize>;
type PartialAssignment = Vec<Option<bool>>;
// (positive occurences, negative occurences, [(clause, index in clause)])
type OccurenceList = Vec<(Cell<usize>, Cell<usize>, Vec<(usize, usize)>)>;

#[derive(Debug)]
pub struct Formula {
	clauses: Vec<Clause>,
	weights: Vec<usize>,
	pub n_vars: usize,
	pub n_clauses: usize,
	pub top: usize
}

#[derive(Debug)]
enum WorkElement {
	// variable, positive
	Pure(usize, bool),
	// literal
	Unit(isize)
}
type WorkStack = Vec<WorkElement>;


/// Computes and applies a renaming so that variable names are in 0..n again
fn compute_renaming(clauses: &mut [Clause]) -> Renaming {
	let renaming: Renaming = clauses.iter()
	                                .flatten()
	                                .map(|l| l.abs() as usize)
	                                .unique()
	                                .enumerate()
	                                .map(|(k, v)| (v, k+1))
	                                .collect();
	
	for clause in clauses.iter_mut() {
		// apply renaming
		for literal in clause {
			let literal_var = literal.abs() as usize;
			let renamed_var = renaming[&literal_var] as isize;
			*literal = literal.signum() * renamed_var;
		}
	}

	renaming
}

impl Formula {
	pub fn preprocess(&mut self) -> (PartialAssignment, Renaming) {
		use crate::parser::WorkElement::*;
		let mut free_list      = vec![true; self.n_vars];
		let mut clause_lengths = self.clauses.iter().map(|c| c.len()).collect::<Vec<_>>();
		let mut occurence_list = self.build_occurence_list(); // should take O(n) where n is the length of the formula
		let mut work_stack     = self.initial_stack(&mut occurence_list, &mut free_list); // O(v + c)

		let mut var_assignment: PartialAssignment = vec![None; self.n_vars];
		while let Some(work) = work_stack.pop() {
			match work {
				Unit(literal) => {
					let var = literal.abs() as usize - 1;
					// make the literal (not the variable) evaluate to true
					var_assignment[var] = Some(literal > 0);
					// remove clauses containing literal and remove ¬literal from clauses
					for &(clause_index, var_index) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						if clause.is_empty() { continue; }

						if clause[var_index] == literal {
							// the clause contains the literal, so the clause can safely be removed
							self.clear_clause(clause_index, &occurence_list, &mut free_list, &mut work_stack);
						} else {
							// remove only the negated literal
							clause[var_index] = 0;
							clause_lengths[clause_index] -= 1;
						}
					} // O(d), where d is maximum degree of variables in formula
					// some clauses may have become unit clauses
					for &(clause_index, _) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						if clause.is_empty() { continue; }

						if clause_lengths[clause_index] == 1 && self.weights[clause_index] == self.top {
							// this is a hard unit clause. find the remaining literal and add it to the work stack
							let unit_literal = *clause.iter().find(|&&l| l != 0).unwrap();
							let unit_index = unit_literal.abs() as usize -1;
							if free_list[unit_index] {
								work_stack.push(Unit(unit_literal));
								free_list[unit_index] = false;
								
								
								for &(clause, _) in &occurence_list[unit_index].2 {
									if self.weights[clause] == self.top && clause_lengths[clause] == 1 {
										// clear any hard unit clause that consists of the same literal. this will
										// keep them from needlessly searching for their only remaining literal
										self.clauses[clause].clear();
									}
								}
							}
						} else if clause_lengths[clause_index] == 0 {
							// there are no literals remaining
							// TODO this should not happen for hard clauses. check that first.
							clause.clear();
						}
					}
				},
				Pure(var, val) => {
					var_assignment[var] = Some(val);
					// empty all clauses containing var, since setting var to val makes them evaluate to true
					for &(clause_index, _) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						if clause.is_empty() { continue; }

						self.clear_clause(clause_index, &occurence_list, &mut free_list, &mut work_stack);
					} // O(d), where d is maximum degree of variables in formula
				}
			} // O(v * d), where v is number of variables
		}

		// remove all erased literals
		for clause in &mut self.clauses {
			clause.retain(|&l| l != 0);
		}
		// remove empty clauses
		self.clauses.retain(|clause| !clause.is_empty());
		// TODO only retain weights of retained clauses

		// rename remaining variables into 1..n
		let renaming = compute_renaming(&mut self.clauses);

		self.n_vars = renaming.len();
		self.n_clauses = self.clauses.len();

		(var_assignment, renaming)
	}
	fn build_occurence_list(&self) -> OccurenceList {
		let mut occ_list = vec![(Cell::new(0), Cell::new(0), Vec::default()); self.n_vars];

		// for all variables find the clauses in which they occure and count their occurences
		for (clause_index, clause) in self.clauses.iter().enumerate() {
			for (index_of_var, &var) in clause.iter().enumerate() {
				let var_index = var.abs() as usize -1;
				// increase count
				if var > 0 {
					occ_list[var_index].0.set(occ_list[var_index].0.get() + 1);
				} else {
					occ_list[var_index].1.set(occ_list[var_index].1.get() + 1);
				}
				// add clause to list and remember where the variable is located in that clause
				occ_list[var_index].2.push((clause_index, index_of_var));
			}
		}

		occ_list
	}
	fn initial_stack(&self, occ_list: &OccurenceList, free_list: &mut Vec<bool>) -> WorkStack {
		use crate::parser::WorkElement::*;

		let mut preprocess_stack = Vec::with_capacity(self.n_vars);
		// push all pure variables on stack
		for i in 0..self.n_vars {
			if occ_list[i].0.get() == 0 {
				// never occures as positive, x_i is false
				preprocess_stack.push(Pure(i, false));
				free_list[i] = false;
			} else if occ_list[i].1.get() == 0 {
				// never occures as negative, x_i is true
				preprocess_stack.push(Pure(i, true));
				free_list[i] = false;
			}
		}
		// TODO also find out if there are any conflicts for the hard clauses
		// push all unit literals on stack
		for i in 0..self.n_clauses {
			let clause = &self.clauses[i];
			let weight = self.weights[i];
			// only consider hard clauses for unit clauses, since they are guaranteed(-ish) to not conflict
			if clause.len() == 0 && weight == self.top {
				let only_var = clause[0];
				let only_var_index = only_var.abs() as usize - 1;
				if free_list[only_var_index] {
					// we didnt add this var as unit or pure already
					preprocess_stack.push(Unit(only_var));
					free_list[only_var_index] = false;
				}
			}
		}

		preprocess_stack
	}
	fn clear_clause(&mut self, clause: usize, occ_list: &OccurenceList, free_list: &mut Vec<bool>,
		stack: &mut WorkStack) {
		use crate::parser::WorkElement::*;

		for &literal in &self.clauses[clause] {
			let literal_index = literal.abs() as usize - 1;
			if literal > 0 {
				// remove positive instance of variable
				occ_list[literal_index].0.set(occ_list[literal_index].0.get() - 1);
				if occ_list[literal_index].0.get() == 0 {
					// we got a new pure literal (negative)
					stack.push(Pure(literal_index, false));
					free_list[literal_index] = false;
				}
			} else {
				// remove negative instance of variable
				occ_list[literal_index].1.set(occ_list[literal_index].1.get() - 1);
				if occ_list[literal_index].1.get() == 0 {
					// we got a new pure literal (positive)
					stack.push(Pure(literal_index, true));
					free_list[literal_index] = false;
				}
			}
		} // O(d)

		self.clauses[clause].clear();
	}
	pub fn sub_formulae(self) -> (Vec<Formula>, Vec<Renaming>) {
		// copy some values
		let clauses = self.clauses.clone();
		let weights = self.weights.clone();
		let top = self.top;

		// use dual graph to find which clauses should stay together
		let intermediate = Dual::from(self);
		let components = connected_components(&intermediate);

		let mut formulae = Vec::with_capacity(components.len());
		let mut renamings = Vec::with_capacity(components.len());

		// decompose into subformulas based on components
		for component in components {
			let mut component_clauses: Vec<_> = component.iter().map(|c| clauses[*c].clone()).collect();
			let component_clause_weights: Vec<_> = component.iter().map(|c| weights[*c]).collect();
			let n_clauses = component_clauses.len();

			let renaming = compute_renaming(&mut component_clauses);
			let n_vars = renaming.len();

			formulae.push(Formula {
				clauses: component_clauses,
				weights: component_clause_weights,
				n_vars,
				n_clauses,
				top
			});

			renamings.push(renaming);
		}


		(formulae, renamings)
	}

	pub fn get_clauses(&self) -> &Vec<Clause> {
		&self.clauses
	}

	pub fn get_weights(&self) -> &Vec<usize> {
		&self.weights
	}

}

impl From<String> for Formula {
	fn from(input: String) -> Formula {
		// get non comment lines
		let mut lines = input.lines().filter(|s| { !s.starts_with('c') });
			
		// parse parameter line
		let p_line = lines.next().expect("parameter line is missing in file");
		let params: Vec<&str> = p_line.split(' ').collect();
		let n_vars = params[2].parse().expect("parameter line is malformed");
		let n_clauses = params[3].parse().expect("parameter line is malformed");
		let top = params[4].parse().expect("parameter line is malformed");

		// parse formula
		let mut formula = Formula {
			clauses: Vec::with_capacity(n_clauses),
			weights: Vec::with_capacity(n_clauses),
			n_vars,
			n_clauses,
			top
		};
		for line in lines {
			let mut values = line.split(' ');
			// weight is the first element of a line
			let weight = values.next().map(|w| w.parse::<usize>().ok()).flatten().expect("file contains empty clause");
			// the rest are the claus
			let values = values.map(|s| s.parse::<isize>().expect("file contains malformed clause"));
			let mut clause: Clause = values.collect();
			// except for the last item, which is always 0
			clause.remove(clause.len() - 1);
			
			formula.clauses.push(clause);
			formula.weights.push(weight);
		}

		formula
	}
}



#[cfg(test)]
mod tests {
	#[test]
	fn test_parameter_parser() {

	}

	#[test]
	fn test_formula_parser() {

	}

	#[test]
	fn test_parser() {

	}
}
