pub struct Formula {
	clauses: Vec<(i32, Vec<i32>)>,
	parameters: Parameters
}

pub struct Parameters {
	n_vars: usize,
	n_clauses: usize,
	top: usize
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
			let weight = values.next().expect("file contains empty claus");
			// the rest are the claus
			let clause = values.collect();
			
			formula.clauses.push((weight, clause))
		}

		formula
	}
}

impl Parameters {
	fn parse_parameters(p_line: &str) -> Parameters {
		let params: Vec<&str> = p_line.split("").collect();
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

