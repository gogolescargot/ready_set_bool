/* ************************************************************************** */
/*                                                                            */
/*                                                        :::      ::::::::   */
/*   main.rs                                            :+:      :+:    :+:   */
/*                                                    +:+ +:+         +:+     */
/*   By: ggalon <ggalon@student.42lyon.fr>          +#+  +:+       +#+        */
/*                                                +#+#+#+#+#+   +#+           */
/*   Created: 2025/01/27 16:51:40 by ggalon            #+#    #+#             */
/*   Updated: 2025/04/15 14:46:38 by ggalon           ###   ########.fr       */
/*                                                                            */
/* ************************************************************************** */

mod test;

use std::collections::HashMap;
use std::fmt;

const MISSING_OPERAND: &str = "Missing operand for !";
const MISSING_RIGHT: &str = "Missing right operand";
const MISSING_LEFT: &str = "Missing left operand";
const INVALID_CHAR: &str = "Invalid character: ";
const INVALID_EXPRESSION: &str = "Invalid RPN expression";
const EMPTY_EXPRESSION: &str = "Empty expression";
const EMPTY_LIST: &str = "Empty list";
const UNSUPPORTED_TYPE: &str = "Unsupported node type";
const INDEX_OFR: &str = "Index out of range";

#[derive(Debug, Clone)]
pub enum AST {
	Variable(char),
	Boolean(bool),
	Negation(Box<AST>),
	And(Box<AST>, Box<AST>),
	Or(Box<AST>, Box<AST>),
	Xor(Box<AST>, Box<AST>),
	Implication(Box<AST>, Box<AST>),
	Equal(Box<AST>, Box<AST>),
}

impl fmt::Display for AST {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			AST::Variable(c) => write!(f, "{}", c),
			AST::Boolean(bool) => write!(f, "{}", if *bool { '1' } else { '0' }),
			AST::Negation(child) => write!(f, "{}!", child),
			AST::And(left, right) => write!(f, "{}{}&", left, right),
			AST::Or(left, right) => write!(f, "{}{}|", left, right),
			AST::Xor(left, right) => write!(f, "{}{}^", left, right),
			AST::Implication(left, right) => write!(f, "{}{}>", left, right),
			AST::Equal(left, right) => write!(f, "{}{}=", left, right),
		}
	}
}

pub fn power(base: u32, exp: u32) -> u32 {
	if exp == 0 {
		return 1;
	}
	let mut result: u32 = 1;
	for _ in 0..exp {
		result *= base;
	}
	return result;
}

pub fn adder(a: u32, b: u32) -> u32 {
	if b == 0 {
		return a;
	}

	let carry = (a & b) << 1;

	return adder(a ^ b, carry);
}

pub fn multiplier(a: u32, b: u32) -> u32 {
	if b == 0 {
		return 0;
	}

	let mut result = a;

	for _ in 1..b {
		result = adder(result, a)
	}

	return result;
}

pub fn gray_code(n: u32) -> u32 {
	return n ^ (n >> 1);
}

// pub fn is_cond(c: char) -> bool
// {
// 	return c == '1' || c == '0'
// }

pub fn is_var(c: char) -> bool {
	return c.is_ascii_uppercase();
}

pub fn is_ops(c: char) -> bool {
	return "!&|^>=".find(c).is_some();
}

pub fn btoc(b: bool) -> char {
	match b {
		true => '1',
		false => '0',
	}
}

// pub fn ctob(c: char) -> bool
// {
// 	match c
// 	{
// 		'1' => true,
// 		'0' => false,
// 		_ => panic!("{}{}", INVALID_CHAR, c),
// 	}
// }

pub fn eval_formula_ast(node: &AST) -> bool {
	match node {
		AST::Boolean(bool) => *bool,
		AST::Negation(child) => !eval_formula_ast(child),
		AST::And(left, right) => eval_formula_ast(left) && eval_formula_ast(right),
		AST::Or(left, right) => eval_formula_ast(left) || eval_formula_ast(right),
		AST::Xor(left, right) => eval_formula_ast(left) ^ eval_formula_ast(right),
		AST::Implication(left, right) => !eval_formula_ast(left) || eval_formula_ast(right),
		AST::Equal(left, right) => eval_formula_ast(left) == eval_formula_ast(right),
		_ => panic!("{}", UNSUPPORTED_TYPE),
	}
}

pub fn eval_formula(formula: &str) -> bool {
	let ast = parse_rpn(formula, false);

	eval_formula_ast(&ast)
}

pub fn to_binary_list(mut num: u32, length: usize) -> Vec<u32> {
	let mut binary_digits = Vec::new();

	if num == 0 {
		binary_digits.push(0);
	}

	while num > 0 {
		binary_digits.push(num % 2);
		num /= 2;
	}

	binary_digits.reverse();

	while binary_digits.len() < length {
		binary_digits.insert(0, 0);
	}

	return binary_digits;
}

pub fn get_variables(formula: &str) -> (HashMap<char, u32>, Vec<char>) {
	let mut vars: HashMap<char, u32> = HashMap::new();
	let mut var_order: Vec<char> = Vec::new();

	for c in formula.chars() {
		if is_var(c) && !vars.contains_key(&c) {
			vars.insert(c, 0);
			var_order.push(c);
		} else if !is_var(c) && !is_ops(c) {
			panic!("{}{}", INVALID_CHAR, c);
		}
	}

	(vars, var_order)
}

pub fn format_header(var_order: &[char]) -> String {
	let mut output = String::new();

	for key in var_order {
		output.push_str(&format!("| {} ", key));
	}
	output.push_str("| = |\n");

	for _ in 0..var_order.len() {
		output.push_str("|---");
	}
	output.push_str("|---|\n");

	output
}

pub fn format_row(vars: &HashMap<char, u32>, var_order: &[char], result: bool) -> String {
	let mut output = String::new();

	for key in var_order {
		if let Some(value) = vars.get(key) {
			output.push_str(&format!("| {} ", value));
		}
	}
	output.push_str(&format!("| {} |\n", btoc(result)));

	output
}

pub fn generate_ast(formula: &str, vars: &HashMap<char, u32>) -> AST {
	let mut temp_str = String::from(formula);

	for (key, value) in vars.iter() {
		temp_str = temp_str.replace(key.to_string().as_str(), value.to_string().as_str());
	}

	parse_rpn(&temp_str, false)
}

pub fn print_truth_table(formula: &str) -> String {
	let mut output = String::new();
	let (mut vars, var_order) = get_variables(formula);

	output.push_str(&format_header(&var_order));

	for i in 0..power(2, var_order.len() as u32) {
		let binary: Vec<u32> = to_binary_list(i, var_order.len());

		for (index, key) in var_order.iter().enumerate() {
			vars.insert(*key, binary[index]);
		}

		let ast = generate_ast(formula, &vars);
		output.push_str(&format_row(&vars, &var_order, eval_formula_ast(&ast)));
	}
	output
}

pub fn parse_rpn(formula: &str, normal: bool) -> AST {
	let mut stack = Vec::new();

	for c in formula.chars() {
		match c {
			'A'..='Z' => stack.push(AST::Variable(c)),
			'0' | '1' => stack.push(AST::Boolean(c == '1')),
			'!' => {
				let operand = stack.pop().expect(MISSING_OPERAND);
				stack.push(negation(operand));
			}
			'&' | '|' | '>' | '=' | '^' => {
				let right = stack.pop().expect(MISSING_RIGHT);
				let left = stack.pop().expect(MISSING_LEFT);

				let node = if normal {
					handle_normal_operator(c, left, right)
				} else {
					handle_standard_operator(c, left, right)
				};

				stack.push(node);
			}
			_ => panic!("{}{}", INVALID_CHAR, c),
		}
	}

	match stack.len() {
		1 => stack.pop().expect(EMPTY_EXPRESSION),
		_ => panic!("{}", INVALID_EXPRESSION),
	}
}

pub fn handle_normal_operator(op: char, left: AST, right: AST) -> AST {
	match op {
		'&' => and(left, right),
		'|' => or(left, right),
		'>' => implication(left, right),
		'=' => equivalence(left, right),
		'^' => xor(left, right),
		_ => unreachable!(),
	}
}

pub fn handle_standard_operator(op: char, left: AST, right: AST) -> AST {
	match op {
		'&' => and(left, right),
		'|' => or(left, right),
		'>' => AST::Implication(boxed(left), boxed(right)),
		'=' => AST::Equal(boxed(left), boxed(right)),
		'^' => AST::Xor(boxed(left), boxed(right)),
		_ => unreachable!(),
	}
}

pub fn boxed(ast: AST) -> Box<AST> {
	Box::new(ast)
}

pub fn negation(operand: AST) -> AST {
	AST::Negation(boxed(operand))
}

pub fn and(left: AST, right: AST) -> AST {
	AST::And(boxed(left), boxed(right))
}

pub fn or(left: AST, right: AST) -> AST {
	AST::Or(boxed(left), boxed(right))
}

pub fn implication(left: AST, right: AST) -> AST {
	or(negation(left), right)
}

pub fn equivalence(left: AST, right: AST) -> AST {
	let left_implies_right = or(negation(left.clone()), right.clone());
	let right_implies_left = or(negation(right), left);
	and(left_implies_right, right_implies_left)
}

pub fn xor(left: AST, right: AST) -> AST {
	let case1 = and(left.clone(), negation(right.clone()));
	let case2 = and(negation(left), right);
	or(case1, case2)
}

pub fn to_nnf(node: AST) -> AST {
	match node {
		AST::Variable(c) => AST::Variable(c),
		AST::Negation(child) => match *child {
			AST::Negation(inner_child) => to_nnf(*inner_child),
			AST::And(left, right) => AST::Or(
				Box::new(to_nnf(AST::Negation(left))),
				Box::new(to_nnf(AST::Negation(right))),
			),
			AST::Or(left, right) => AST::And(
				Box::new(to_nnf(AST::Negation(left))),
				Box::new(to_nnf(AST::Negation(right))),
			),
			other => AST::Negation(Box::new(to_nnf(other))),
		},
		AST::And(left, right) => AST::And(Box::new(to_nnf(*left)), Box::new(to_nnf(*right))),
		AST::Or(left, right) => AST::Or(Box::new(to_nnf(*left)), Box::new(to_nnf(*right))),
		_ => panic!("{}", UNSUPPORTED_TYPE),
	}
}

pub fn collect_literals(node: AST, literals: &mut Vec<AST>) {
	match node {
		AST::Or(left, right) => {
			collect_literals(*left, literals);
			collect_literals(*right, literals);
		}
		_ => literals.push(node),
	}
}

pub fn build_right_associative_or(literals: Vec<AST>) -> AST {
	let mut literals = literals.into_iter().collect::<Vec<_>>();
	if literals.is_empty() {
		panic!("{}", EMPTY_LIST);
	}
	let mut current = literals.pop().expect(EMPTY_LIST);
	while let Some(lit) = literals.pop() {
		current = AST::Or(Box::new(lit), Box::new(current));
	}
	current
}

pub fn collect_clauses(node: AST, clauses: &mut Vec<AST>) {
	match node {
		AST::And(left, right) => {
			collect_clauses(*left, clauses);
			collect_clauses(*right, clauses);
		}
		_ => clauses.push(node),
	}
}

pub fn build_right_associative_and(clauses: Vec<AST>) -> AST {
	let mut clauses = clauses.into_iter().collect::<Vec<_>>();
	if clauses.is_empty() {
		panic!("{}", EMPTY_LIST);
	}
	let mut current = clauses.pop().expect(EMPTY_LIST);
	while let Some(clause) = clauses.pop() {
		current = AST::And(Box::new(clause), Box::new(current));
	}
	current
}

pub fn to_cnf(node: AST) -> AST {
	match node {
		AST::Variable(c) => AST::Variable(c),
		AST::Negation(child) => AST::Negation(child),
		AST::And(left, right) => {
			let left_cnf = to_cnf(*left);
			let right_cnf = to_cnf(*right);
			let mut clauses = Vec::new();
			collect_clauses(left_cnf, &mut clauses);
			collect_clauses(right_cnf, &mut clauses);
			build_right_associative_and(clauses)
		}
		AST::Or(left, right) => {
			let left_cnf = to_cnf(*left);
			let right_cnf = to_cnf(*right);
			match (left_cnf, right_cnf) {
				(AST::And(a, b), c) => {
					let or1 = AST::Or(a, Box::new(c.clone()));
					let or2 = AST::Or(b, Box::new(c));
					AST::And(Box::new(to_cnf(or1)), Box::new(to_cnf(or2)))
				}
				(a, AST::And(b, c)) => {
					let or1 = AST::Or(Box::new(a.clone()), b);
					let or2 = AST::Or(Box::new(a), c);
					AST::And(Box::new(to_cnf(or1)), Box::new(to_cnf(or2)))
				}
				(a, b) => {
					let mut literals = Vec::new();
					collect_literals(a, &mut literals);
					collect_literals(b, &mut literals);
					build_right_associative_or(literals)
				}
			}
		}
		_ => panic!("{}", UNSUPPORTED_TYPE),
	}
}

pub fn negation_normal_form(formula: &str) -> String {
	let ast = parse_rpn(formula, true);
	let nnf_ast = to_nnf(ast);
	nnf_ast.to_string()
}

pub fn conjunctive_normal_form(formula: &str) -> String {
	let ast = parse_rpn(formula, true);
	let nnf_ast = to_nnf(ast);
	let cnf_ast = to_cnf(nnf_ast);
	cnf_ast.to_string()
}

pub fn sat(formula: &str) -> bool {
	let mut vars = get_variables(formula).0;

	let keys: Vec<char> = vars.keys().cloned().collect();

	for i in 0..power(2, vars.len() as u32) {
		let binary: Vec<u32> = to_binary_list(i, vars.len());

		for (index, key) in keys.iter().enumerate() {
			vars.insert(*key, binary[index]);
		}

		let ast = generate_ast(formula, &vars);

		if eval_formula_ast(&ast) {
			return true;
		}
	}

	false
}

pub fn powerset(set: Vec<i32>) -> Vec<Vec<i32>> {
	let mut result: Vec<Vec<i32>> = vec![vec![]];

	for num in set {
		let mut subset = Vec::new();

		for set in &result {
			let mut subset_temp = set.clone();
			subset_temp.push(num);
			subset.push(subset_temp);
		}

		result.extend(subset);
	}

	result
}

pub fn set_universe(sets: &Vec<Vec<i32>>) -> Vec<i32> {
	let mut universe = Vec::new();

	for set in sets {
		for elem in set {
			if !universe.contains(elem) {
				universe.push(*elem);
			}
		}
	}

	universe
}

pub fn set_negation(set: &Vec<i32>, universe: &Vec<i32>) -> Vec<i32> {
	let result: Vec<i32> = universe.clone();
	result.into_iter().filter(|x| !set.contains(x)).collect()
}

pub fn set_and(left: &Vec<i32>, right: &Vec<i32>) -> Vec<i32> {
	let result: Vec<i32> = left.clone();
	result.into_iter().filter(|x| right.contains(x)).collect()
}

pub fn set_or(left: &Vec<i32>, right: &Vec<i32>) -> Vec<i32> {
	let mut result: Vec<i32> = left.clone();
	result.extend(right.into_iter().filter(|x| !left.contains(x)));
	result
}

pub fn set_xor(left: &Vec<i32>, right: &Vec<i32>, universe: &Vec<i32>) -> Vec<i32> {
	let case1 = set_and(left, &set_negation(right, universe));
	let case2 = set_and(&set_negation(left, universe), right);
	set_or(&case1, &case2)
}

pub fn set_implication(left: &Vec<i32>, right: &Vec<i32>, universe: &Vec<i32>) -> Vec<i32> {
	set_or(&set_negation(left, universe), right)
}

pub fn set_equivalence(left: &Vec<i32>, right: &Vec<i32>, universe: &Vec<i32>) -> Vec<i32> {
	let left_implies_right = set_or(&set_negation(left, universe), right);
	let right_implies_left = set_or(left, &set_negation(right, universe));
	set_and(&left_implies_right, &right_implies_left)
}

pub fn eval_set_ast(node: &AST, sets: &Vec<Vec<i32>>, universe: &Vec<i32>) -> Vec<i32> {
	match node {
		AST::Variable(c) => {
			let index = *c as usize - 65;
			if index >= sets.len() {
				panic!("{}", INDEX_OFR);
			}
			sets[index].clone()
		}
		AST::Negation(child) => {
			let child_set = eval_set_ast(child, sets, universe);
			set_negation(&child_set, universe)
		}
		AST::And(left, right) => {
			let left_set = eval_set_ast(left, sets, universe);
			let right_set = eval_set_ast(right, sets, universe);
			set_and(&left_set, &right_set)
		}
		AST::Or(left, right) => {
			let left_set = eval_set_ast(left, sets, universe);
			let right_set = eval_set_ast(right, sets, universe);
			set_or(&left_set, &right_set)
		}
		AST::Xor(left, right) => {
			let left_set = eval_set_ast(left, sets, universe);
			let right_set = eval_set_ast(right, sets, universe);
			set_xor(&left_set, &right_set, universe)
		}
		AST::Implication(left, right) => {
			let left_set = eval_set_ast(left, sets, universe);
			let right_set = eval_set_ast(right, sets, universe);
			set_implication(&left_set, &right_set, universe)
		}
		AST::Equal(left, right) => {
			let left_set = eval_set_ast(left, sets, universe);
			let right_set = eval_set_ast(right, sets, universe);
			set_equivalence(&left_set, &right_set, universe)
		}
		_ => panic!("{}", UNSUPPORTED_TYPE),
	}
}

pub fn eval_set(formula: &str, sets: Vec<Vec<i32>>) -> Vec<i32> {
	let ast = parse_rpn(formula, false);
	let universe = set_universe(&sets);
	eval_set_ast(&ast, &sets, &universe)
}

pub fn interleave(n: u16) -> u32 {
	let mut x = n as u32;
	x = (x | (x << 8)) & 0x00FF00FF;
	x = (x | (x << 4)) & 0x0F0F0F0F;
	x = (x | (x << 2)) & 0x33333333;
	x = (x | (x << 1)) & 0x55555555;
	x
}

pub fn reverse_interleave(n: u32) -> (u16, u16) {
	let mut x = n & 0x55555555;
	x = (x | (x >> 1)) & 0x33333333;
	x = (x | (x >> 2)) & 0x0F0F0F0F;
	x = (x | (x >> 4)) & 0x00FF00FF;
	x = (x | (x >> 8)) & 0x0000FFFF;

	let mut y = (n >> 1) & 0x55555555;
	y = (y | (y >> 1)) & 0x33333333;
	y = (y | (y >> 2)) & 0x0F0F0F0F;
	y = (y | (y >> 4)) & 0x00FF00FF;
	y = (y | (y >> 8)) & 0x0000FFFF;

	(x as u16, y as u16)
}

pub fn map(x: u16, y: u16) -> f64 {
	let result = (interleave(x) | (interleave(y) << 1)) as f64;
	result / u32::MAX as f64
}

pub fn reverse_map(n: f64) -> (u16, u16) {
	let result = n * u32::MAX as f64;
	reverse_interleave(result as u32)
}

pub fn main() {}
