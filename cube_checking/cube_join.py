from eznf import modeler
import argparse

argparser = argparse.ArgumentParser()
argparser.add_argument(
    "-f", "--formula", required=True, type=str, help="CNF Formula file"
)
argparser.add_argument("-c", "--cubes", required=True, type=str, help="Cube file")
argparser.add_argument("-o", "--output", required=False, type=str, help="Output file")
argparser.add_argument(
    "--tautcheck", action="store_true", help="Checks for a tautology"
)
argparser.add_argument('--inccnf', action="store_true", help="Creates a .icnf file with the formula + cubes")


args = argparser.parse_args()

formula_file = args.formula
cube_file = args.cubes
output_file = args.output
tautcheck = args.tautcheck
icnf = args.inccnf

encoding = modeler.Modeler()

def itokenize(line):
    """
    takes a line as a string, coming from either a `p cnf` or a `p inccnf` file
    returns array of ints without 0
    ignores lines starting with c or p
    """
    if len(line) == 0:
        return []
    if line[0] == "c" or line[0] == "p":
        return []
    if line[:-1] == "\n":
        line = line[:-1]
    tokens = line.split(" ")
    ans = []
    for t in tokens:
        try:
            t = int(t)
            if t != 0:
                ans.append(t)
        except ValueError:
            continue
    return ans


with open(formula_file, 'r', encoding='utf-8') as sb_file:
    for line in sb_file.readlines():
        tkns = itokenize(line)
        if len(tkns) > 0:
            encoding.add_clause(tkns)


cubes = []
with open(cube_file, 'r', encoding='utf-8') as cb_file:
    for line in cb_file.readlines():
        tkns = itokenize(line)
        if len(tkns) == 0:
            continue
        if tautcheck:
            encoding.add_clause([-t for t in tkns])
        else:
            cubes.append(tkns)

if tautcheck:
    encoding.serialize(output_file)
elif icnf:
    encoding.cube_and_conquer(lambda: cubes, output_file)
else:
    assert len(cubes) == 1
    cube = cubes[0]
    for lit in cube:
        encoding.add_clause([lit])
    encoding.serialize(output_file)
