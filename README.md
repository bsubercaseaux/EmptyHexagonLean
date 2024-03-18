# EmptyHexagonLean
A Lean verification of the _Empty Hexagon Number_, obtained by a [recent breakthrough of Heule and Scheucher](https://arxiv.org/abs/2403.00737).
The main theorem is that every finite set of 30 or more points must contain a convex and empty 6-gon. The proof is based on generating a CNF formula whose unsatisfiability is formally proved to imply the theorem. This repository contains the formalization code, and it allows the generation of the associated CNF.



## Installing Lean

See [the manual](https://lean-lang.org/lean4/doc/setup.html),
or potentially [the community website](https://leanprover-community.github.io/get_started.html).


## Building the Lean formalization

The Lean code is in the `Lean/` folder. In this folder run:
```
lake exe cache get # Downloads pre-built .olean files for mathlib
lake build         # Builds this project's main theorems
```

The main results are in
- `Lean/Geo/Hexagon/TheMainTheorem.lean`
- `Lean/Geo/Naive/TheMainTheorem.lean`


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

For `k = 6`, `n = 30`, the CNF takes on the order of 17,000 CPU hours to show UNSAT.

## Authors
- [Bernardo Subercaseaux](https://bsubercaseaux.github.io/) (Carnegie Mellon University)
- [Wojciech Nawrocki](https://voidma.in/) (Carnegie Mellon University)
- [James Gallicchio](https://gallicch.io/index.html) (Carnegie Mellon University)
- [Cayden Codel](http://crcodel.com/) (Carnegie Mellon University)
- [Mario Carneiro](https://digama0.github.io/) (Carnegie Mellon University)
- [Marijn J. H. Heule](https://www.cs.cmu.edu/~mheule/) (Carnegie Mellon University)
