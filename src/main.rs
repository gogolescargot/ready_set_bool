/* ************************************************************************** */
/*                                                                            */
/*                                                        :::      ::::::::   */
/*   main.rs                                            :+:      :+:    :+:   */
/*                                                    +:+ +:+         +:+     */
/*   By: ggalon <ggalon@student.42lyon.fr>          +#+  +:+       +#+        */
/*                                                +#+#+#+#+#+   +#+           */
/*   Created: 2025/01/27 16:51:40 by ggalon            #+#    #+#             */
/*   Updated: 2025/01/27 18:53:05 by ggalon           ###   ########.fr       */
/*                                                                            */
/* ************************************************************************** */

use std::iter::Enumerate;

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

fn main() {
	println!("{}", adder(2, 3));
	println!("{}", multiplier(2, 10));
	println!("{}", gray_code(7));
	println!("{}", eval_formula("11>"));
}
