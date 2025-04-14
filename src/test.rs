use crate::adder;
use crate::multiplier;
use crate::gray_code;
use crate::eval_formula;
use crate::print_truth_table;
use crate::negation_normal_form;
use crate::conjunctive_normal_form;
use crate::sat;
use crate::powerset;
use crate::eval_set;

#[test]
fn test_adder(){
	let test_cases = vec![
		((1, 2), 3),
		((1, 0), 1),
		((0, 1), 1),
		((99, 1), 100),
	];

	for (input, expected) in test_cases {
		let result = adder(input.0, input.1);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_multiplier(){
	let test_cases = vec![
		((2, 4), 8),
		((1, 0), 0),
		((0, 1), 0),
		((0, 0), 0),
		((99, 10), 990),
	];

	for (input, expected) in test_cases {
		let result = multiplier(input.0, input.1);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_gray_code(){
    let test_cases = vec![
        (0, 0),
        (1, 1),
        (2, 3),
        (3, 2),
        (4, 6),
        (5, 7),
        (6, 5),
        (7, 4),
		(8, 12),
    ];

	for (input, expected) in test_cases {
		let result = gray_code(input);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_eval_formula() {
    let test_cases = vec![
        ("10&", false),
        ("10|", true),
        ("11>", true),
        ("10=", false),
        ("1011||=", true)
    ];

    for (input, expected) in test_cases {
        let result = eval_formula(input);
        assert_eq!(result, expected);
    }
}

#[test]
fn test_print_truth_table() {    
    let test_cases = vec![
        ("AB&C|", "| A | B | C | = |\n|---|---|---|---|\n| 0 | 0 | 0 | 0 |\n| 0 | 0 | 1 | 1 |\n| 0 | 1 | 0 | 0 |\n| 0 | 1 | 1 | 1 |\n| 1 | 0 | 0 | 0 |\n| 1 | 0 | 1 | 1 |\n| 1 | 1 | 0 | 1 |\n| 1 | 1 | 1 | 1 |\n"),
    ];

    for (input, expected) in test_cases {
        let result = print_truth_table(input);
        assert_eq!(result, expected);
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
		let result = negation_normal_form(input);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_cnf() {
	let test_cases = vec![
		("AB&!", "A!B!|"),
		("AB|!", "A!B!&"),
		("A!!", "A"),
		("AB|C&", "AB|C&"),
		("AB|C|D|", "ABCD|||"),
		("AB&C&D&", "ABCD&&&"),
		("AB&!C!|", "A!B!C!||"),
		("AB|!C!&", "A!B!C!&&")
	];

	for (input, expected) in test_cases {
		let result = conjunctive_normal_form(input);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_sat() {
	let test_cases = vec![
		("AB|", true),
		("AB&", true),
		("AA!&", false),
		("AA^", false)
	];

	for (input, expected) in test_cases {
		let result = sat(input);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_powerset() {
	let test_cases = vec![
		(vec![], vec![vec![]]),
		(vec![1], vec![vec![], vec![1]]),
		(vec![1, 2], vec![vec![], vec![1], vec![2], vec![1, 2]]),
		(vec![1, 2, 3], vec![vec![], vec![1], vec![2], vec![1, 2], vec![3], vec![1, 3], vec![2, 3], vec![1, 2, 3]]),
	];

	for (input, expected) in test_cases {
		let result = powerset(input);
		assert_eq!(result, expected);
	}
}

#[test]
fn test_eval_set() {
    let test_cases: Vec<(&str, Vec<Vec<i32>>, Vec<i32>)> = vec![
        ("A", vec![vec![1, 2, 3]], vec![1, 2, 3]),
        ("A!", vec![vec![1, 2, 3]], vec![]),
        
        ("AB&", vec![vec![1, 2, 3], vec![2, 3, 4]], vec![2, 3]),
        ("AB|", vec![vec![1, 2, 3], vec![2, 3, 4]], vec![1, 2, 3, 4]),
        ("AB^", vec![vec![1, 2, 3], vec![2, 3, 4]], vec![1, 4]),
        ("AB>", vec![vec![1, 2, 3], vec![2, 3, 4]], vec![4, 2, 3]),
        ("AB=", vec![vec![1, 2, 3], vec![2, 3, 4]], vec![2, 3]),
        
        ("AB&C|", vec![vec![1, 2], vec![2, 3], vec![3, 4]], vec![2, 3, 4]),
        ("ABC&&", vec![vec![1, 2, 3], vec![2, 3, 4], vec![1, 3, 5]], vec![3]),
        ("AB|C&", vec![vec![1, 2], vec![3, 4], vec![2, 4]], vec![2, 4]),
        
        ("A", vec![vec![]], vec![]),
        ("A!", vec![vec![]], vec![]),
        ("AB&", vec![vec![1, 2], vec![]], vec![]),
        ("AB|", vec![vec![1, 2], vec![]], vec![1, 2]),
    ];

    for (formula, sets, expected) in test_cases {
        let result = eval_set(formula, sets);
        assert_eq!(result, expected);
    }
}