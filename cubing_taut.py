from eznf import modeler
import argparse

argparser = argparse.ArgumentParser()
argparser.add_argument("-c", "--cubes", required=True, type=str, help="Cube file")
argparser.add_argument("-s", "--symmetry", required=True, type=str, help="Symmetry breaking clause file")

args = argparser.parse_args()
cube_file = args.cubes
symmetry_breaking_file = args.symmetry

encoding = modeler.Modeler()
encoding.load(symmetry_breaking_file)


def itokenize(line):
    if line[:-1] == '\n':
        line = line[:-1]
    tokens = line.split(' ')
    ans = []
    for t in tokens:
        try:
            t = int(t)
            if t == 0: continue
            ans.append(t)
        except:
            continue
    return ans


with open(cube_file, 'r') as cb_file:
    for line in cb_file.readlines():
        tkns = itokenize(line)
        encoding.add_clause([-t for t in tkns])

encoding.serialize("cube_tautology.cnf")
