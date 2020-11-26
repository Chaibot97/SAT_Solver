# CDCL SAT Solver

Authors: Lizhou Cai, Junrui Liu


A conflict-driver SAT solver enhanced with the following extensions:

- UIP clause learning and non-chronological backtracking
- Clause forgetting
- Watched literals
- Exponential VSIDS
- Phase saving
- Reluctant doubling sequence for restarts

## Dependencies
* `python` version 3.7+
* `cython` version 0.29.21
* Apple `clang` version 12.0.0


## Build
We initially developed the project in Python. But because efficiency is a central concern, we translated the library part of the project into Cython by adding static type annotations.

Both the original Python code and the translated Cython version are present. The former ends with extension `.py`, and the latter with `.pyx` or `.pxd`. The CLI program `src/main.py` is written in pure Python 3 so that it is able to call either version:

- To use the optimized Cython version, build the project with `make`. This compiles the library into `.so` files, which the driver `src/main.py` will be able to detect and import without any additional modification.
- To use the original Python version, run `make clean` before running the driver.


## Usage


    src/main.py DIMACS_FILE

The program will print out either 
* `unsat` if the input CNF formula is unsatisfiable, or
* `sat` and a model of the formula.


## Benchmarking

Beside the three supplied benchmark sets, we generated additional benchmarks using the scheme developed in NeuroSAT.

Given `n`, the desired number of variables, the generator samples random clauses until the overall formula becomes unsatisfiable. Negating one literal in the last sampled clause yields a SAT formula. The sat and unsat are added to the test set as a pair, and `n` is drawn from a uniform distribution specified by the user.

Our custom benchmarks are generated using the following parameters, ordered by increasing difficulty

- `bench5`: 39 pairs of formulas with variables drawn from `U(3, 10)`
- `bench6`: 40 pairs, `U(5, 100)`
- `bench7`: medium-difficulty subset of `bench4` with `n` between 116 and 152
- `bench4`: 200 pairs, `U(5, 200)`