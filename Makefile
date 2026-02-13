NAME := computorv1

.PHONY: all clean fclean re test

all $(NAME):
	cargo build --release

clean fclean:
	cargo clean

re: fclean all

test:
	cargo test

doc:
	cargo doc --open