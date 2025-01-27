/* ************************************************************************** */
/*                                                                            */
/*                                                        :::      ::::::::   */
/*   main.rs                                            :+:      :+:    :+:   */
/*                                                    +:+ +:+         +:+     */
/*   By: ggalon <ggalon@student.42lyon.fr>          +#+  +:+       +#+        */
/*                                                +#+#+#+#+#+   +#+           */
/*   Created: 2025/01/27 16:51:40 by ggalon            #+#    #+#             */
/*   Updated: 2025/04/09 14:16:35 by ggalon           ###   ########.fr       */
/*                                                                            */
/* ************************************************************************** */

use std::collections::HashMap;

fn adder(x: u32, y: u32) -> u32
{
	if y == 0
	{
		return x;
	}
	
	let carry = (x & y) << 1;

	return adder(x ^ y, carry)
}

fn multiplier(a: u32, b: u32) -> u32
{
	let mut result = a;

	for _ in 1..b
	{
		result = adder(result, a)
	}
	
	return result
}

fn gray_code(n: u32) -> u32
{
	return n ^ (n >> 1)
}

fn is_cond(c: char) -> bool
{
	return c == '1' || c == '0'
}

fn is_var(c: char) -> bool
{
	return c.is_ascii_uppercase()
}

fn is_ops(c: char) -> bool
{
	return "!&|^>=".find(c).is_some()
}

fn btoc(b: bool) -> char
{
	match b
	{
		true=>'1',
		false=>'0',
	}	
}

fn ctob(c: char) -> bool
{
	match c
	{
		'1' => true,
		'0' => false,
		_ => panic!("Invalid character: {}", c),
	}	
}

fn eval_formula(formula: &str) -> bool
{
	let mut stack: Vec<char> = Vec::new();

	for c in formula.chars()
	{
		if is_cond(c)
		{
			stack.push(c);
		}
		else
		{
			if stack.len() < 2
			{
				panic!("Wrong formula operands number");
			}

			let op1 = ctob(stack.pop().expect("Stack underflow"));
			let op2 = ctob(stack.pop().expect("Stack underflow"));

			match c
			{
				'!'=>stack.push(btoc(op1 != op2)),
				'&'=>stack.push(btoc(op1 && op2)),
				'|'=>stack.push(btoc(op1 || op2)),
				'^'=>stack.push(btoc(op1 ^ op2)),
				'>'=>stack.push(btoc(!op1 || op2)),
				'='=>stack.push(btoc(op1 == op2)),
				_ => panic!("Invalid character found: {}", c),
			}
		}
	}

	if stack.len() != 1
	{
		panic!("Wrong formula size at the end of computation");
	}

	return ctob(stack[0])
}

fn to_binary_list(mut num: u32, length: usize) -> Vec<u32>
{
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

	return binary_digits
}

fn print_header(vars: &HashMap<char, u32>)
{
	for key in vars.keys()
	{
		print!("| {} ", key);
	}
	println!("| = |");
	for _ in 0..vars.len()
	{
		print!("|---");
	}
	println!("|---|");
}

fn print_row(vars: &HashMap<char, u32>, result: bool)
{
	for value in vars.values()
	{
		print!("| {} ", value);
	}
	println!("| {} |", btoc(result));
}

fn print_truth_table(formula: &str)
{
	let mut vars: HashMap<char, u32> = HashMap::new();

	for c in formula.chars()
	{
		if is_var(c)
		{
			vars.insert(c, 0);
		}
		else if !is_ops(c)
		{
			panic!("Invalid character found: {}", c);
		}
	}

	print_header(&vars);

	let keys: Vec<char> = vars.keys().cloned().collect();

	for i in 0..2_u32.pow(vars.len() as u32)
	{
		let binary  = to_binary_list(i, vars.len());

		for (index, key) in keys.iter().enumerate()
		{
			vars.insert(*key, binary[index]);
		}

		let mut temp_str = String::from(formula);

		for (key, value) in vars.iter()
		{		
			temp_str = temp_str.replace(key.to_string().as_str(), value.to_string().as_str());
		}

		print_row(&vars, eval_formula(&temp_str));
	}
}

// fn expand_formula(formula: &str)
// {

// }

// fn main() {
// 	// println!("{}", adder(2, 3));
// 	// println!("{}", multiplier(2, 10));
// 	// println!("{}", gray_code(7));
// 	// println!("{}", eval_formula("11>"));
// 	print_truth_table("AB&C|");
// 	eval_formula("10|");
// }

use std::fmt;
use std::str::Chars;

#[derive(Debug, Clone)]
enum AST {
	Variable(char),
	Negation(Box<AST>),
	And(Box<AST>, Box<AST>),
	Or(Box<AST>, Box<AST>),
}

impl fmt::Display for AST {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			AST::Variable(c) => write!(f, "{}", c),
			AST::Negation(child) => write!(f, "{}!", child),
			AST::And(left, right) => write!(f, "{}{}&", left, right),
			AST::Or(left, right) => write!(f, "{}{}|", left, right),
		}
	}
}

fn parse_rpn(s: &str) -> Result<AST, String> {
	let mut stack: Vec<AST> = Vec::new();
	let mut iter = s.chars();

	while let Some(c) = iter.next() {
		match c {
			'A'..='Z' => stack.push(AST::Variable(c)),
			'!' => {
				let operand = stack.pop().ok_or("Missing operand for !".to_string())?;
				stack.push(AST::Negation(Box::new(operand)));
			}
			'&' | '|' | '>' | '=' | '^' => {
				let right = stack.pop().ok_or("Missing right operand".to_string())?;
				let left = stack.pop().ok_or("Missing left operand".to_string())?;

				match c {
					'&' => stack.push(AST::And(Box::new(left), Box::new(right))),
					'|' => stack.push(AST::Or(Box::new(left), Box::new(right))),
					'>' => {
						// Implication: A > B → !A | B
						let not_left = AST::Negation(Box::new(left));
						stack.push(AST::Or(Box::new(not_left), Box::new(right)));
					}
					'=' => {
						// Equivalence: A = B → (!A | B) & (!B | A)
						let left1 = AST::Negation(Box::new(left.clone()));
						let left2 = AST::Or(Box::new(left1), Box::new(right.clone()));
						let right1 = AST::Negation(Box::new(right));
						let right2 = AST::Or(Box::new(right1), Box::new(left));
						stack.push(AST::And(Box::new(left2), Box::new(right2)));
					}
					'^' => {
						// XOR: A ^ B → (A & !B) | (!A & B)
						let case1 = AST::And(
							Box::new(left.clone()),
							Box::new(AST::Negation(Box::new(right.clone()))),
						);
						let case2 = AST::And(
							Box::new(AST::Negation(Box::new(left))),
							Box::new(right),
						);
						stack.push(AST::Or(Box::new(case1), Box::new(case2)));
					}
					_ => unreachable!(),
				}
			}
			_ => return Err(format!("Invalid character: {}", c)),
		}
	}

	if stack.len() != 1 {
		Err("Invalid RPN expression".to_string())
	} else {
		stack.pop().ok_or("Empty expression".to_string())
	}
}

fn to_nnf(node: AST) -> AST {
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
	}
}

fn nnf(formula: &str) -> Result<String, String> {
	let ast = parse_rpn(formula)?;
	let nnf_ast = to_nnf(ast);
	Ok(nnf_ast.to_string())
}

fn main() {
	let test_cases = vec![
		("AB&!", "A!B!|"),
		("AB|!", "A!B!&"),
		("A!!", "A"),
		("AB>", "A!B|"),
		("A", "A"),
		("AB^", "AB!&A!B&|"),
	];

	for (input, expected) in test_cases {
		match nnf(input) {
			Ok(result) => {
				println!("Input: {}", input);
				println!("Output: {}", result);
				println!("Expected: {}", expected);
				assert_eq!(result, expected);
				println!("Passed\n");
			}
			Err(e) => panic!("Error for {}: {}", input, e),
		}
	}
}

#[test]
fn test_nnf() {
	let test_cases = vec![
		("AB&!", "A!B!|"),
		("AB|!", "A!B!&"),
		("A!!", "A"),
		("AB>", "A!B|"),
		("A", "A"),
		("AB^", "AB!&A!B&|"),
	];

	for (input, expected) in test_cases {
		let result = match nnf(input) {
			Ok(res) => res,
			Err(e) => panic!("Error for {}: {}", input, e),
		};
		assert_eq!(result, expected);
	}
}