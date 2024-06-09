#!/usr/bin/env sh
# Receives the desired cube number as $1

gcc 6hole-cube.c -o cube_gen
./cube_gen $1 vars.out > .tmp_cube_$1
python3 cube_join.py -f 6-30.cnf -c .tmp_cube_$1 -o with_cube_$1.cnf
cadical with_cube_$1.cnf proof_cube_$1.lrat --lrat
cake_lpr with_cube_$1.cnf proof_cube_$1.lrat

rm with_cube_$1.cnf proof_cube_$1.lrat .tmp_cube_$1
