.PHONY: test clippy docker-shell nix-shell benchmarks benchmark docs

test:
	cargo test

clippy:
	cargo clippy --all-targets --all-features -- -D warnings

docker-shell:
	docker build -t rust-curves .
	docker run -it rust-curves bash

nix-shell:
	nix-shell

benchmarks:
	cargo criterion --bench all_benchmarks

# BENCHMARK should be one of the [[bench]] names in Cargo.toml
benchmark:
	cargo criterion --bench ${BENCH}

docs:
	cd docs && mdbook serve --open
