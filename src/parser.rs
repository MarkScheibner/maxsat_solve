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
enum WorkElement {
	// variable, positive
	Pure(usize),
	// literal
	Unit(isize)
}
type WorkStack = Vec<WorkElement>;


#[derive(Debug)]
pub struct Formula {
	clauses: Vec<Clause>,
	weights: Vec<usize>,
	pub n_vars: usize,
	pub n_clauses: usize,
	pub top: usize
}

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
	/// Applies some preprocessing to the formula. After the preprocessing is done, the formula will contain no
	/// pure variables and no unit clauses and no empty clauses.
	pub fn preprocess(&mut self) -> Option<(PartialAssignment, Renaming)> {
		// n = number of vars, m = number of clauses, l = length of formula,
		// d_v = number of clauses that contain variable v
		use crate::parser::WorkElement::*;
		let mut assignment = vec![None; self.n_vars];                                       // O(n)
		let mut clause_lengths = self.clauses.iter().map(|c| c.len()).collect::<Vec<_>>();  // O(m)
		let mut occurence_list = self.build_occurence_list();                               // O(l)
		let mut work_stack     = self.initial_stack(&mut occurence_list, &mut assignment)?; // O(n + m)

		while let Some(work) = work_stack.pop() {
			match work {
				Unit(literal) => {
					let var = literal.abs() as usize - 1;
					// remove clauses containing literal and remove ¬literal from clauses
					for &(clause_index, var_index) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						if clause.is_empty() { continue; }

						if clause[var_index] == literal {
							// the clause contains the literal, so the clause can safely be removed
							self.clear_clause(clause_index, &occurence_list, &mut assignment, &mut work_stack);
						} else {
							// the clause contains the negated literal, remove only that
							clause[var_index] = 0;
							clause_lengths[clause_index] -= 1;
							if clause_lengths[clause_index] == 0 {
								// there are no literals remaining
								if self.weights[clause_index] == self.top {
									// which is bad if this is a hard clause
									return None;
								}
								clause.clear();
							}
						}
					} // O(d_var)
					// some clauses may have become unit clauses. we must check for this after we are done iterating
					// since otherwise two clauses containing the same literal may become unit after each other and
					// we would then have to inspect both
					for &(clause_index, _) in &occurence_list[var].2 {
						let clause = &mut self.clauses[clause_index];
						if clause.is_empty() { continue; }

						if clause_lengths[clause_index] == 1 && self.weights[clause_index] == self.top {
							// this is a hard unit clause. find the remaining literal and add it to the work stack. If
							// we already "pay" for stepping through the clause at the moment we set a literal to 0 we
							// can do this in O(1)
							let unit_literal = *clause.iter().find(|&&l| l != 0).unwrap();
							let unit_var = unit_literal.abs() as usize -1;
							if assignment[unit_var].is_none() {
								work_stack.push(Unit(unit_literal));
								assignment[unit_var] = Some(unit_literal > 0);
							}
							// we must clear any (hard) unit clause that consists of the same literal so that the above
							// claim actually holds. otherwise we cant move the cost to where the literal is set to 0
							for &(clause, var_index) in &occurence_list[unit_var].2 {
								let contained_literal = self.clauses[clause][var_index];
								if clause_lengths[clause] == 1 && contained_literal == literal {
									// unit clause contains the same literal, so we can also clear the clause
									self.clauses[clause].clear();
								} else if self.weights[clause] == self.top && contained_literal == -literal {
									// we have unit clauses that disagree on the unit variable
									return None;
								}
							} // this is essentially free, since we would do this anyways inside the first loop
						}
					} // O(d_var)
				},
				Pure(var) => {
					// empty all clauses containing var, since setting var to val makes them evaluate to true
					for &(clause_index, _) in &occurence_list[var].2 {
						self.clear_clause(clause_index, &occurence_list, &mut assignment, &mut work_stack);
					} // O(d_var)
				}
			} // O(sum(d_v)) = O(l) 
		}

		// remove all erased literals
		for clause in &mut self.clauses {
			clause.retain(|&l| l != 0);
		} // O(l)
		// remove empty clauses and their weight
		let mut retain = self.clauses.iter().map(|clause| !clause.is_empty()); // O(m)
		self.weights.retain(|_| retain.next().unwrap_or(false));               // O(m)
		self.clauses.retain(|clause| !clause.is_empty());                      // O(m)

		// rename remaining variables into 1..n
		let renaming = compute_renaming(&mut self.clauses);                    // O(l)

		self.n_vars = renaming.len();
		self.n_clauses = self.clauses.len();

		// done after O(l)
		Some((assignment, renaming))
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
	fn initial_stack(&self, occ_list: &OccurenceList, assignment: &mut PartialAssignment) -> Option<WorkStack> {
		use crate::parser::WorkElement::*;

		let mut preprocess_stack = Vec::with_capacity(self.n_vars);
		// push all pure variables on stack
		for i in 0..self.n_vars {
			if occ_list[i].0.get() == 0 {
				// never occures as positive, x_i is false
				preprocess_stack.push(Pure(i));
				assignment[i] = Some(false);
			} else if occ_list[i].1.get() == 0 {
				// never occures as negative, x_i is true
				preprocess_stack.push(Pure(i));
				assignment[i] = Some(true);
			}
		}
		// push all unit literals on stack
		for i in 0..self.n_clauses {
			let clause = &self.clauses[i];
			let weight = self.weights[i];
			// only consider hard clauses for unit clauses, since they are guaranteed(-ish) to not conflict
			if clause.len() == 1 && weight == self.top {
				let only_literal = clause[0];
				let only_var = only_literal.abs() as usize - 1;
				if let Some(assigned) = assignment[only_var] {
					// variable already has a value, check for conflict
					if assigned != (only_literal > 0) {
						return None;
					}
				} else {
					// we didnt add this var as unit or pure already
					preprocess_stack.push(Unit(only_literal));
					assignment[only_var] = Some(only_literal > 0);
				}
			}
		}

		Some(preprocess_stack)
	}
	fn clear_clause(&mut self, clause: usize, occ_list: &OccurenceList, assignment: &mut PartialAssignment,
		stack: &mut WorkStack) {
		use crate::parser::WorkElement::*;

		for &literal in &self.clauses[clause] {
			// ignore literals marked as removed
			if literal == 0 { continue; }

			let variable = literal.abs() as usize - 1;
			// the variable will already be removed completely, so the count doesn't matter anymore
			if assignment[variable].is_some() { continue; }
			
			if literal > 0 {
				// remove positive instance of variable
				occ_list[variable].0.set(occ_list[variable].0.get() - 1);
				if occ_list[variable].0.get() == 0 {
					// we got a new pure literal (negative, as no positive instance remains)
					stack.push(Pure(variable));
					assignment[variable] = Some(false);
				}
			} else {
				// remove negative instance of variable
				occ_list[variable].1.set(occ_list[variable].1.get() - 1);
				if occ_list[variable].1.get() == 0 {
					// we got a new pure literal (positive, as no negative instance remains)
					stack.push(Pure(variable));
					assignment[variable] = Some(true);
				}
			}
		} // may take O(n), but repeated calls to this function may only accumulate costs of up to O(l)

		self.clauses[clause].clear();
	}
	
	pub fn split(self) -> (Vec<Formula>, Vec<Renaming>) {
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
