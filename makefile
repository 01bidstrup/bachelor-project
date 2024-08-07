.PHONY: run build

run: 
	@dune exec -- ./run/main.exe
build:
	clear
	dune build
	clear 
	dune build
test:
	dune test

format:
	opam exec -- dune fmt