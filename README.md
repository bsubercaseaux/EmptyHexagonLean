# EmptyHexagonLean
A Lean verification of the _Empty Hexagon Number_, obtained by a [recent breakthrough of Heule and Scheucher](https://arxiv.org/abs/2403.00737).
The main theorem is that every finite set of 30 or more points must contain a convex, empty 6-gon. The proof is based on generating a CNF formula whose unsatisfiability is formally proved to imply the theorem. This repository contains the formalization code, and it allows the generation of the associated CNF.



## Installing Lean

The main part of this repository is a mathematical formalization written in the Lean 4 theorem prover.
To install Lean on your machine,
see the [quickstart](https://lean-lang.org/lean4/doc/quickstart.html) guide from the Lean manual,
or [the extended setup instructions](https://lean-lang.org/lean4/doc/setup.html).


## Building the Lean formalization

The Lean code is in the `Lean/` folder. In this folder run:
```
lake exe cache get   # Downloads pre-built .olean files for mathlib
lake build           # Builds this project's main theorems
```

The main results are in
- `Lean/Geo/Hexagon/TheMainTheorem.lean`
- `Lean/Geo/Naive/TheMainTheorem.lean`

Overall structure:
- `Lean/Geo/Definitions` defines orientations and develops a theory of combinatorial geometry.
- `Lean/Geo/Canonicalization` proves that a set of points can be mapped to a 'canonical' set of points with the same orientations.
- `Lean/Geo/KGon` defines the 'base' encoding, which is a shared component of both the naive encoding and the specialized hexagon encoding.
- `Lean/Geo/Naive` defines the naive encoding and proves the main results based on it.
- `Lean/Geo/Hexagon` defines the specialized encoding and proves main results based on it.
- `Lean/Geo/RunEncoding.lean` gives a CLI for running the various encodings and outputting the resulting CNFs.
- `Lean/Geo/SAT`, `Lean/Geo/ToMathlib` both contain components that morally belong in libraries on which we depend.


## Generating CNFs

The project includes scripts for generating the CNFs we formalized against. These must be run inside the `Lean` subfolder.

#### Convex 6-gon
For `n` points, in the `Lake/` directory, run:
```
lake exe encode gon 6 <n>
```
With `n = 17` this CNF can be solved in under a minute on most machines.

#### Convex `k`-hole
For convex `k`-hole in `n` points, in the `Lake/` directory, run:
```
lake exe encode hole <k> <n>
```

For `k = 3, 4, 5` on `n = 3, 5, 10` respectively,
the CNFs produced can be shown UNSAT instantly.

For `k = 6`, `n = 30`, the CNF takes on the order of 17,000 CPU hours to show UNSAT when parallelized using cube&conquer.

# Cube and Conquer verification

In order to verify that the resulting formula $F$ is indeed UNSAT, two things ought to be checked:

 1) **(Tautology proof)** The formula $F$ is UNSAT iff $F \land C_i$ is UNSAT for every $i$.
 2) **(UNSAT proof)** For each cube $C_i$, the formula $F \land C_i$ is UNSAT.

This repository contains scripts that allow you to check these two proofs.

The **tautology proof** is implied by checking that $F \land (\bigwedge_i \neg C_i)$ is UNSAT, as per Section 7.3 of [Heule and Scheucher](https://arxiv.org/abs/2403.00737).

As a first step, install the required dependencies:
1) Clone and compile the SAT solver `cadical` from [its GitHub repository](https://github.com/arminbiere/cadical). Add the `cadical` executable to your `PATH`.
2) Clone and compile the verified proof checker `cake_lpr` from [its GitHub repository](https://github.com/tanyongkiam/cake_lpr). Add the `cake_lpr` executable to your `PATH`.
3) Install the `eznf` and `lark` python libraries with `pip install eznf` and `pip install lark`.

Next, generate the main CNF by running:
```
cd Lean
lake exe encode hole 6 30 ../cube_checking/vars.out > ../cube_checking/6-30.cnf
```

The **tautology proof** can be verified by navigating to the `cube_checking/` directory and running 
```
./verify_tautology.sh
```
which boils down to:
```
gcc 6hole-cube.c -o cube_gen
./cube_gen 0 vars.out > cubes.icnf
python3 cube_join.py -f 6-30.cnf -c cubes.icnf --tautcheck -o taut_if_unsat.cnf
cadical taut_if_unsat.cnf tautology_proof.lrat --lrat # this should take around 30 seconds
cake_lpr taut_if_unsat.cnf tautology_proof.lrat
```
If proof checking succeeds, you should see the following output:

```
s VERIFIED UNSAT
```

Because verifying the **UNSAT proof** requires many thousands of CPU hours,
we provide a simple way to verify that any single cube is UNSAT.
To generate the formula + cube number $i$ (assuming the steps for the **tautology proof** have been followed), run `./solve_cube.sh` script in the `cube_checking/` directory, which essentially runs:
```
./cube_gen <i> vars.out > .tmp_cube_<i>
python3 cube_join.py -f 6-30.cnf -c .tmp_cube_<i> -o with_cube_<i>.cnf
cadical with_cube_<i>.cnf proof_cube_<i>.lrat --lrat # this should take a few seconds
cake_lpr with_cube_<i>.cnf proof_cube_<i>.lrat
```
For example, to solve cube number 42, run:

```
./solve_cube.sh 42
```
The cubes are indexed from 1 to 312418.

We **DO NOT RECOMMEND** that the casual verifier runs all cubes,
as doing so would take many thousands of CPU hours.
Our verification was completed in a semi-efficient manner using parallel computation,
which required some custom scripting.
However, the skeptical reviewer with *lots of computation to spare* can replicate our results.
To generate the formula and all cubes for incremental solving, run:
```
./cube_gen 0 vars.out > cubes.icnf
python3 cube_join.py -f 6-30.cnf -c cubes.icnf --inccnf -o full_computation.icnf
cadical full_computation.icnf # this should take a while :P
```

## Authors
- [Bernardo Subercaseaux](https://bsubercaseaux.github.io/) (Carnegie Mellon University)
- [Wojciech Nawrocki](https://voidma.in/) (Carnegie Mellon University)
- [James Gallicchio](https://gallicch.io/index.html) (Carnegie Mellon University)
- [Cayden Codel](https://crcodel.com/) (Carnegie Mellon University)
- [Mario Carneiro](https://digama0.github.io/) (Carnegie Mellon University)
- [Marijn J. H. Heule](https://www.cs.cmu.edu/~mheule/) (Carnegie Mellon University)
