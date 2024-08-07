
This is a reupload of the original private gitlab.au repository

Credit
- Thomas Lyhne Hansen
- Markus Bidstrup Jakobsen

# bachelor-project
This is the implementation of the ploymorphic type checker for our bachelors project
## Dependencies
To run the implementation it is required that you have `OCaml` and `dune` installed. We also use `OUnit2` for our tests which is required. 

Additionally we have set up tasks in a `makefile` so it is recommended to have `make` installed.

## How to run
Call `make test` to run all unit and integration tests.

Call `make run` to run the system tests. This includes the 3 examples from the paper as well as 3 additional examples of the pair indexing functions being used.
