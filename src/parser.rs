type WeightedClause = (usize, Vec<isize>);

pub struct Formula {
	clauses: Vec<WeightedClause>,
	parameters: Parameters
}

pub struct Parameters {
	pub n_vars: usize,
	pub n_clauses: usize,
	pub top: usize
}

impl Formula {
	pub fn new(input: String) -> Formula {
		// get non comment lines
		let mut lines = input.lines().filter(|s| { !s.starts_with('c') });
			
		// parse parameter line
		let p_line = lines.next().expect("parameter line is missing in file");
		let parameters = Parameters::parse_parameters(p_line);

		// parse formula
		let mut formula = Formula {
			clauses: Vec::with_capacity(parameters.n_clauses),
			parameters
		};
		for line in lines {
			let mut values = line.split(' ');
			// weight is the first element of a line
			let weight = values.next().map(|w| w.parse::<usize>().ok()).flatten().expect("file contains empty clause");
			// the rest are the claus
			let values = values.map(|s| s.parse::<isize>().expect("file contains malformed clause"));
			let mut clause: Vec<isize> = values.collect();
			// except for the last item, which is always 0
			clause.remove(clause.len() - 1);
			
			formula.clauses.push((weight, clause))
		}

		formula
	}

	pub fn unit_propagation(&mut self) {
		// TODO rename variables of clause when variable is removed
		
		loop {
			// find hard unit-clauses
			// TODO find out if we can do something similar for soft clauses
			let mut single: Vec<_> = self.clauses.iter().enumerate()
			                                     .filter(|(_, (w, c))| *w == self.parameters.top && c.len() == 1)
			                                     .map(|(i, (_, c))| (i, c[0]))
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

			// we no longer care for index of unit-clauses
			let single: MetroHashSet<_> = single.iter().map(|(_, c)| *c).collect();
			// retain only clauses containing none of the literals
			self.clauses.retain(|(_, c)| !c.iter().any(|l| single.contains(l)));
			// retain only literals whose complement is not one of the unit-clauses
			for (_, c) in &mut self.clauses {
				c.retain(|l| !single.contains(&-l));
			}

		}

		self.parameters.n_clauses = self.clauses.len();
	}

	pub fn get_clauses(&self) -> &Vec<WeightedClause> {
		&self.clauses
	}

	pub fn get_parameters(&self) -> &Parameters {
		&self.parameters
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
