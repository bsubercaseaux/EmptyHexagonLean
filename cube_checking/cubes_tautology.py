from eznf import modeler
import argparse
import os
argparser = argparse.ArgumentParser()
argparser.add_argument("-c", "--cubes", required=True, type=str, help="Cube file")
argparser.add_argument("-f", "--formula", required=True, type=str, help="CNF Formula file")

args = argparser.parse_args()
cube_file = args.cubes
formula_file = args.formula

encoding = modeler.Modeler()

# takes a line as a string of either `p cnf` or  `p inccnf` and returns array of ints without 0
def itokenize(line):
    if line[:-1] == '\n':
        line = line[:-1]
    tokens = line.split(' ')
    ans = []
    for t in tokens:
        try:
            t = int(t)
            if t != 0:
                ans.append(t)
        except:
            continue
    return ans


with open(formula_file, 'r') as sb_file:
    for line in sb_file.readlines():
        tkns = itokenize(line)
        assert len(tkns) > 0
        encoding.add_clause(tkns)

with open(cube_file, 'r') as cb_file:
    for line in cb_file.readlines():
        tkns = itokenize(line)
        assert len(tkns) > 0
        encoding.add_clause([-t for t in tkns])



OUT_FILENAME = "cube_taut_check.cnf"
print(f"\nFormula representing the validity of the cubes: {os.getcwd() + '/' + OUT_FILENAME}")
encoding.serialize(OUT_FILENAME)
print("The formula should be UNSAT, and take around 15 seconds with Kissat")
