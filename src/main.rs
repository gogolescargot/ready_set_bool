/* ************************************************************************** */
/*                                                                            */
/*                                                        :::      ::::::::   */
/*   main.rs                                            :+:      :+:    :+:   */
/*                                                    +:+ +:+         +:+     */
/*   By: ggalon <ggalon@student.42lyon.fr>          +#+  +:+       +#+        */
/*                                                +#+#+#+#+#+   +#+           */
/*   Created: 2025/01/27 16:51:40 by ggalon            #+#    #+#             */
/*   Updated: 2025/04/11 15:06:24 by ggalon           ###   ########.fr       */
/*                                                                            */
/* ************************************************************************** */

mod test;

use std::fmt;
use std::collections::HashMap;

const MISSING_OPERAND: &str = "Missing operand for !";
const MISSING_RIGHT: &str = "Missing right operand";
const MISSING_LEFT: &str = "Missing left operand";
const INVALID_CHAR: &str = "Invalid character: ";
const INVALID_EXPRESSION: &str = "Invalid RPN expression";
const EMPTY_EXPRESSION: &str = "Empty expression";
const EMPTY_LIST: &str = "Empty list";
const UNSUPPORTED_TYPE: &str = "Unsupported node type";

#[derive(Debug, Clone)]
enum AST {
    Variable(char),
	Boolean(bool),
    Negation(Box<AST>),
    And(Box<AST>, Box<AST>),
    Or(Box<AST>, Box<AST>),
	Xor(Box<AST>, Box<AST>),
	Implication(Box<AST>, Box<AST>),
	Equal(Box<AST>, Box<AST>)
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

fn adder(a: u32, b: u32) -> u32
{
	if b == 0
	{
		return a;
	}
	
	let carry = (a & b) << 1;

	return adder(a ^ b, carry)
}

fn multiplier(a: u32, b: u32) -> u32
{
	if b == 0
	{
		return 0;
	}
	
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

// fn is_cond(c: char) -> bool
// {
// 	return c == '1' || c == '0'
// }

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

// fn ctob(c: char) -> bool
// {
// 	match c
// 	{
// 		'1' => true,
// 		'0' => false,
// 		_ => panic!("{}{}", INVALID_CHAR, c),
// 	}	
// }

fn eval_formula_ast(node: &AST) -> bool
{
	match node
	{
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

fn eval_formula(formula: &str) -> bool
{
    let ast = parse_rpn(formula, false);

    eval_formula_ast(&ast)
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

fn get_variables(formula: &str) -> (HashMap<char, u32>, Vec<char>)
{
    let mut vars: HashMap<char, u32> = HashMap::new();
    let mut var_order: Vec<char> = Vec::new();

    for c in formula.chars()
    {
        if is_var(c) && !vars.contains_key(&c)
        {
            vars.insert(c, 0);
            var_order.push(c);
        }
        else if !is_var(c) && !is_ops(c)
        {
            panic!("{}{}", INVALID_CHAR, c);
        }
    }

    (vars, var_order)
}

fn format_header(var_order: &[char]) -> String
{
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

fn format_row(vars: &HashMap<char, u32>, var_order: &[char], result: bool) -> String
{
    let mut output = String::new();
    
    for key in var_order {
        if let Some(value) = vars.get(key) {
            output.push_str(&format!("| {} ", value));
        }
    }
    output.push_str(&format!("| {} |\n", btoc(result)));
    
    output
}

fn generate_ast(formula: &str, vars: &HashMap<char, u32>) -> AST
{
	let mut temp_str = String::from(formula);

	for (key, value) in vars.iter()
	{		
		temp_str = temp_str.replace(key.to_string().as_str(), value.to_string().as_str());
	}

	parse_rpn(&temp_str, false)
}

fn print_truth_table(formula: &str) -> String
{
    let mut output = String::new();
    let (mut vars, var_order) = get_variables(formula);

    output.push_str(&format_header(&var_order));

    for i in 0..2_u32.pow(var_order.len() as u32)
    {
        let binary: Vec<u32> = to_binary_list(i, var_order.len());

        for (index, key) in var_order.iter().enumerate()
        {
            vars.insert(*key, binary[index]);
        }

        let ast = generate_ast(formula, &vars);
        output.push_str(&format_row(&vars, &var_order, eval_formula_ast(&ast)));
    }
    output
}

fn parse_rpn(formula: &str, normal: bool) -> AST {
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

fn handle_normal_operator(op: char, left: AST, right: AST) -> AST {
    match op {
        '&' => and(left, right),
        '|' => or(left, right),
        '>' => implication(left, right),
        '=' => equivalence(left, right),
        '^' => xor(left, right),
        _ => unreachable!(),
    }
}

fn handle_standard_operator(op: char, left: AST, right: AST) -> AST {
    match op {
        '&' => and(left, right),
        '|' => or(left, right),
        '>' => AST::Implication(boxed(left), boxed(right)),
        '=' => AST::Equal(boxed(left), boxed(right)),
        '^' => AST::Xor(boxed(left), boxed(right)),
        _ => unreachable!(),
    }
}

fn boxed(ast: AST) -> Box<AST> {
    Box::new(ast)
}

fn negation(operand: AST) -> AST {
    AST::Negation(boxed(operand))
}

fn and(left: AST, right: AST) -> AST {
    AST::And(boxed(left), boxed(right))
}

fn or(left: AST, right: AST) -> AST {
    AST::Or(boxed(left), boxed(right))
}

fn implication(left: AST, right: AST) -> AST {
    or(negation(left), right)
}

fn equivalence(left: AST, right: AST) -> AST {
    let left_implies_right = or(negation(left.clone()), right.clone());
    let right_implies_left = or(negation(right), left);
    and(left_implies_right, right_implies_left)
}

fn xor(left: AST, right: AST) -> AST {
    let case1 = and(left.clone(), negation(right.clone()));
    let case2 = and(negation(left), right);
    or(case1, case2)
}

fn to_nnf(node: AST) -> AST
{
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
		_ => panic!("{}", UNSUPPORTED_TYPE)
    }
}

fn collect_literals(node: AST, literals: &mut Vec<AST>)
{
    match node {
        AST::Or(left, right) => {
            collect_literals(*left, literals);
            collect_literals(*right, literals);
        }
        _ => literals.push(node),
    }
}

fn build_right_associative_or(literals: Vec<AST>) -> AST
{
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

fn collect_clauses(node: AST, clauses: &mut Vec<AST>)
{
    match node {
        AST::And(left, right) => {
            collect_clauses(*left, clauses);
            collect_clauses(*right, clauses);
        }
        _ => clauses.push(node),
    }
}

fn build_right_associative_and(clauses: Vec<AST>) -> AST
{
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

fn to_cnf(node: AST) -> AST
{
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
		_ => panic!("{}", UNSUPPORTED_TYPE)
    }
}

fn negation_normal_form(formula: &str) -> String
{
	let ast = parse_rpn(formula, true);
	let nnf_ast = to_nnf(ast);
	nnf_ast.to_string()
}

fn conjunctive_normal_form(formula: &str) -> String
{
    let ast = parse_rpn(formula, true);
    let nnf_ast = to_nnf(ast);
    let cnf_ast = to_cnf(nnf_ast);
    cnf_ast.to_string()
}

fn sat(formula: &str) -> bool
{
	let mut vars = get_variables(formula).0;

	let keys: Vec<char> = vars.keys().cloned().collect();

	for i in 0..2_u32.pow(vars.len() as u32)
	{
		let binary: Vec<u32>  = to_binary_list(i, vars.len());

		for (index, key) in keys.iter().enumerate()
		{
			vars.insert(*key, binary[index]);
		}

		let ast = generate_ast(formula, &vars);

		if eval_formula_ast(&ast)
		{
			return true;
		}
	}

	false

}

fn main() {

}
