#!/usr/bin/env sh

DIR=$PWD

## Generate CNF formula for k=6, n=30
## vars.out will contain the variable mapping that makes the Lean encoding
## compatible with the C code for cube generation
cd ../Lean/
echo "Generating CNF formula for n=30, k=6..."
lake exe encode hole 6 30 $DIR/vars.out > $DIR/6-30.cnf

## Generate all cubes, using the variable mapping
cd $DIR
echo "Generating cubes..."
gcc 6hole-cube.c -o cube_gen
./cube_gen 0 vars.out > cubes.icnf

## Combine formula + negation of every cube
echo "Combining formula and cubes..."
python3 cubes_tautology.py -f 6-30.cnf -c cubes.icnf

