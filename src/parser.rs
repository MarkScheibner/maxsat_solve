use metrohash::{MetroHashSet, MetroHashMap};
use itertools::Itertools;
use crate::graph::{Dual, connected_components};

type Clause = Vec<isize>;
type Renaming = MetroHashMap<usize, usize>;
type PartialAssignment = Vec<Option<bool>>;
// (still free, positive occurences, negative occurences, clauses)
type PreprocessList = Vec<(usize, usize, Vec<usize>)>;

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

enum PreprocessStackElement {
	// variable, negative
	Pure(usize, bool),
	// literal
	Unit(isize)
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
		use crate::parser::PreprocessStackElement::*;
		let mut occurence_list: PreprocessList = vec![(0, 0, Vec::default()); self.parameters.n_vars];
		let mut still_free = vec![true; self.parameters.n_vars];
		// build occurence list: for all variables find the clauses in which they occure and count their occurences
		for (clause_index, clause) in self.clauses.iter().enumerate() {
			for &var in clause {
				let var_index = var.abs() as usize -1;
				// increase count
				if var > 0 { occurence_list[var_index].0 += 1; } else {	occurence_list[var_index].1 += 1; }
				// add clause to list
				// TODO also save index of variable in clause
				occurence_list[var_index].2.push(clause_index);
			}
		} // should take O(n) where n ist the length of the formula

		let mut preprocess_stack: Vec<PreprocessStackElement> = Vec::with_capacity(self.parameters.n_vars);
		// push all pure variables on stack
		for i in 0..self.parameters.n_vars {
			if occurence_list[i].0 == 0 {
				// never occures as positive literal
				preprocess_stack.push(Pure(i, false));
				still_free[i] = false;
			} else if occurence_list[i].1 == 0 {
				// never occures as negative literal
				preprocess_stack.push(Pure(i, true));
				still_free[i] = false;
			}
		}
		// push all unit literals on stack
		for i in 0..self.parameters.n_clauses {
			let clause = &self.clauses[i];
			let weight = self.weights[i];
			// only consider hard clauses for unit clauses, since they are guaranteed(-ish) to not conflict
			if clause.len() == 0 && weight == self.parameters.top {
				let only_var = clause[0];
				let only_var_index = only_var.abs() as usize - 1;
				if still_free[only_var_index] {
					// we didnt add this var as unit already
					preprocess_stack.push(Unit(only_var));
					still_free[only_var_index] = false;
				}
			}
		}

		let mut partial_assignment: PartialAssignment = vec![None; self.parameters.n_vars];
		while let Some(work) = preprocess_stack.pop() {
			match work {
				Unit(literal) => {

				},
				Pure(var, neg) => {
					partial_assignment[var] = Some(!neg);
					// empty all clauses containing var, since setting var to !neg makes them true
					for &clause_index in &occurence_list[var].2 {
						self.clauses[clause_index].clear();
					}
				}
			}
		}

		// TODO remove all empty clauses

		// rename remaining variables into 1..n
		let renaming = compute_renaming(&mut self.clauses);

		(partial_assignment, renaming)
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
