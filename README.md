# Combo


> **Warning**
> Tests need to be improved, tests solvers have been implemented but they are extremely simple because it takes a lot of time to make a solver. So the fact that the program works correctly is not at all clear.


## How to use the lib

- Import the module
- Write a formula with the type inside the module (only functions, variables and constants work). The formula must be a conjunction of atomic formula.
- Create a array with theories (A theory is a combination of kinds, functions, variables and a solver that returns SAT with contraints or UNSAT)
- Execute the solve entry function
