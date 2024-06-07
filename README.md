# EmptyHexagonLean
A Lean verification of the _Empty Hexagon Number_, obtained by a [recent breakthrough of Heule and Scheucher](https://arxiv.org/abs/2403.00737).
The main theorem is that every finite set of 30 or more points must contain a convex and empty 6-gon. The proof is based on generating a CNF formula whose unsatisfiability is formally proved to imply the theorem. This repository contains the formalization code, and it allows the generation of the associated CNF.



## Installing Lean

See the [quickstart](https://lean-lang.org/lean4/doc/quickstart.html) guide from the Lean manual,
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

The project includes scripts for generating the CNFs we formalized against.

#### Convex 6-gon
For `n` points:
```
lake exe encode gon 6 <n>
```
With `n = 17` this CNF can be solved in under a minute on most machines.

#### Convex `k`-hole
For convex `k`-hole in `n` points:
```
lake exe encode hole <k> <n>
```

For `k = 3, 4, 5` on `n = 3, 5, 10` respectively,
the CNFs produced can be shown UNSAT instantly.

For `k = 6`, `n = 30`, the CNF takes on the order of 17,000 CPU hours to show UNSAT when parallelized using cube&conquer.

# Cube and Conquer verification

In order to verify that the resulting formula $F$ is indeed UNSAT, two things ought to be checked:
1) The formula $F$ is UNSAT iff $F \land C_i$ is UNSAT for every $i$.
2) For each cube $C_i$, the formula $F \land C_i$ is UNSAT.


Note that step 1) is implied by checking that $F \land (\bigwedge_i \neg C_i)$ is UNSAT; a "tautology proof", as per Section 7.3 of Heule and Scheucher.
Step 1) can be verified by running
```
cd cube_checking
sh check_tautology.sh
kissat cube_taut_check.cnf tautology_proof.drat
drat-trim cube_taut_check.cnf tautology_proof.drat -f -l proof.lrat

```
Note that this requires the SAT solver [kissat](https://github.com/arminbiere/kissat) be in the path, and also [DRAT-trim](https://github.com/marijnheule/drat-trim).
The LRAT proof should be checkable with the verified checker [cake_lpr](https://github.com/tanyongkiam/cake_lpr).

## Authors
- [Bernardo Subercaseaux](https://bsubercaseaux.github.io/) (Carnegie Mellon University)
- [Wojciech Nawrocki](https://voidma.in/) (Carnegie Mellon University)
- [James Gallicchio](https://gallicch.io/index.html) (Carnegie Mellon University)
- [Cayden Codel](https://crcodel.com/) (Carnegie Mellon University)
- [Mario Carneiro](https://digama0.github.io/) (Carnegie Mellon University)
- [Marijn J. H. Heule](https://www.cs.cmu.edu/~mheule/) (Carnegie Mellon University)
