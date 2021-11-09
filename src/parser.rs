use std::cell::Cell;

use metrohash::{MetroHashSet, MetroHashMap};
use itertools::Itertools;
use crate::graph::{Dual, connected_components};

type Clause = Vec<isize>;
type Renaming = MetroHashMap<usize, usize>;
type PartialAssignment = Vec<Option<bool>>;
// (still free, positive occurences, negative occurences, clauses)
type OccurenceList = Vec<(Cell<usize>, Cell<usize>, Vec<(usize, usize)>)>;

#[derive(Debug)]
pub struct Formula {
	clauses: Vec<Clause>,
	weights: Vec<usize>,
	parameters: Parameters
}

#[derive(Debug)]
pub struct Parameters {
	pub n_vars: usize,
	pub n_clauses: usize,
	pub top: usize
}

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
	/// Preprocesses the formula by unit progagation. After this step the formula will contain no unit-clauses
	/// # Returns
	/// A vector containing the renaming and a vector containing the removed literals
	pub fn unit_propagation(&mut self) -> (Renaming, Vec<isize>) {
		let mut removed: Vec<isize> = Vec::new();

		loop {
			// find hard unit-clauses
			let mut single: Vec<_> = self.clauses.iter().enumerate()
			                                     .filter(|(i, c)| self.weights[*i] == self.parameters.top && c.len() == 1)
			                                     .map(|(i, c)| (i, c[0]))
			                                     .collect();
			
			if single.is_empty() { 
				// no unit-clauses were found, so we're done
				break;
			}
			
			// TODO find inconsistencies

			// remove hard unit-clauses
			single.reverse();
			for (i, _) in &single {
				self.clauses.swap_remove(*i);
			}

			let single: MetroHashSet<_> = single.iter().map(|(_, c)| *c).collect();
			// retain only clauses containing none of the literals
			self.clauses.retain(|c| !c.iter().any(|l| single.contains(l)));
			// retain only literals whose complement is not one of the unit-clauses
			for c in &mut self.clauses {
				c.retain(|l| !single.contains(&-l));
			}
			
			single.iter().for_each(|l| removed.push(*l));

		}
		
		// calculate renaming: list variables and rename based on order
		let renaming = compute_renaming(&mut self.clauses);

		self.parameters.n_vars = renaming.len();
		self.parameters.n_clauses = self.clauses.len();
		
		(renaming, removed)
	}

	pub fn preprocess(&mut self) -> (PartialAssignment, Renaming) {
		use crate::parser::WorkElement::*;
		let mut occurence_list = self.build_occurence_list(); // should take O(n) where n is the length of the formula
		let mut still_free = vec![true; self.parameters.n_vars];
		let mut work_stack = self.initial_stack(&mut occurence_list, &mut still_free); // O(v + c)
		let mut index_mapping: MetroHashMap<(usize, usize), usize> = MetroHashMap::default(); // TODO initialize this

		let mut partial_assignment: PartialAssignment = vec![None; self.parameters.n_vars];
		while let Some(work) = work_stack.pop() { 
			match work {
				Unit(literal) => {
					let literal_index = literal.abs() as usize - 1;
					// make the literal (not the variable) evaluate to true
					partial_assignment[literal_index] = Some(literal > 0);

					for &(var_index, clause_index) in &occurence_list[literal_index].2 {
						let clause = &mut self.clauses[clause_index];
						// see if clause is already gone
						if clause.is_empty() { continue; }

						// its not gone, so empty the clause or remove the negated literal
						if clause[var_index] == literal {
							self.clear_clause(clause_index, &occurence_list, &mut still_free, &mut work_stack);
						} else {
							// the clause contains the negated literal, so we only remove that
							clause.swap_remove(var_index);
							if clause.len() == 1 {
								// we got a new unit clause
								work_stack.push(Unit(clause[0]))
							}
							// update index of var which is now at var_index
							// TODO
							
						}
					} // O(d), where d is maximum degree of variables in formula
				},
				Pure(var, val) => {
					partial_assignment[var] = Some(val);
					// empty all clauses containing var, since setting var to val makes them evaluate to true
					for &(_, clause_index) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						// see if clause is already gone
						if clause.is_empty() { continue; }

						// otherwise clear it
						self.clear_clause(clause_index, &occurence_list, &mut still_free, &mut work_stack);
					} // O(d), where d is maximum degree of variables in formula
				}
			} // O(v * d), where v is number of variables
		}

		// remove all empty clauses
		self.clauses.retain(|clause| !clause.is_empty());

		// rename remaining variables into 1..n
		let renaming = compute_renaming(&mut self.clauses);

		(partial_assignment, renaming)
	}
	fn build_occurence_list(&self) -> OccurenceList {
		let mut occ_list = vec![(Cell::new(0), Cell::new(0), Vec::default()); self.parameters.n_vars];

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

		let mut preprocess_stack = Vec::with_capacity(self.parameters.n_vars);
		// push all pure variables on stack
		for i in 0..self.parameters.n_vars {
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
		for i in 0..self.parameters.n_clauses {
			let clause = &self.clauses[i];
			let weight = self.weights[i];
			// only consider hard clauses for unit clauses, since they are guaranteed(-ish) to not conflict
			if clause.len() == 0 && weight == self.parameters.top {
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
		let top = self.parameters.top;

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
				parameters: Parameters {
					n_vars,
					n_clauses,
					top
				}
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

	pub fn get_parameters(&self) -> &Parameters {
		&self.parameters
	}
}

impl From<String> for Formula {
	fn from(input: String) -> Formula {
		// get non comment lines
		let mut lines = input.lines().filter(|s| { !s.starts_with('c') });
			
		// parse parameter line
		let p_line = lines.next().expect("parameter line is missing in file");
		let parameters = Parameters::parse_parameters(p_line);

		// parse formula
		let mut formula = Formula {
			clauses: Vec::with_capacity(parameters.n_clauses),
			weights: Vec::with_capacity(parameters.n_clauses),
			parameters
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

impl Parameters {
	fn parse_parameters(p_line: &str) -> Parameters {
		let params: Vec<&str> = p_line.split(' ').collect();
		let n_vars = params[2].parse().expect("parameter line is malformed");
		let n_clauses = params[3].parse().expect("parameter line is malformed");
		let top = params[4].parse().expect("parameter line is malformed");
		Parameters {
			n_vars,
			n_clauses,
			top
		}
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
