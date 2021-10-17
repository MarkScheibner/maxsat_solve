type WeightedClause = (u32, Vec<i32>);

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
			let mut values = line.split(' ')
			                     .map(|s| s.parse::<i32>().expect("file contains malformed clause"));
			// weight is the first element of a line
			let weight = values.next().expect("file contains empty clause");
			// the rest are the claus
			let clause = values.collect();
			
			formula.clauses.push((weight as u32, clause))
		}

		formula
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
