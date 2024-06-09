#!/bin/sh 

gcc 6hole-cube.c -o cube_gen
./cube_gen 0 vars.out > cubes.icnf
python3 cube_join.py -f 6-30.cnf -c cubes.icnf --tautcheck -o taut_if_unsat.cnf
${CADICAL:-cadical} taut_if_unsat.cnf tautology_proof.lrat --lrat
${CAKELPR:-cake_lpr} taut_if_unsat.cnf tautology_proof.lrat
