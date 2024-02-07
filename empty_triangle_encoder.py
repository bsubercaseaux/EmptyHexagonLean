from eznf import modeler # this is my library for encodings, it's similar to PySAT.
import itertools

N = 4 # number of points

def encode(N):
    triples = list(itertools.combinations(range(N), 3)) # all possible ordered triples of points
    quadruples = list(itertools.combinations(range(N), 4)) # all possible ordered quadruples of points
    
    Z = modeler.Modeler() # create a modeler object, just the way of using my library
    
    for triple in triples:
        a, b, c = triple
        Z.add_var(f's_{a, b, c}', description=f"signotope of points {a}, {b}, {c}")
        
#    for quadruple in quadruples:
#        a, b, c, d = quadruple
#        Z.constraint(f'-s_{a, b, c} or -s_{a, c, d} or s_{a, b, d}')
#        Z.constraint(f'-s_{a, b, c} or -s_{b, c, d} or s_{a, c, d}')
#        Z.constraint(f's_{a, b, c} or s_{a, c, d} or -s_{a, b, d}')
#        Z.constraint(f's_{a, b, c} or s_{b, c, d} or -s_{a, c, d}')

    for triple in triples:
        a, b, c = triple
        for x in range(a + 1, b): # x < b
            Z.add_var(f'inside_{x, a, b, c}', description=f"{x} is inside the triangle {a, b, c}")
            Z.constraint(f"inside_{x, a, b, c} <-> ((s_{a, b, c} <-> s_{a, x, c}) & (-s_{a, x, b} <-> s_{a, b, c}))")
        for x in range(b+1,  c): # x > b
            Z.add_var(f'inside_{x, a, b, c}', description=f"{x} is inside the triangle {a, b, c}")
            Z.constraint(f"inside_{x, a, b, c} <-> ((s_{a, b, c} <-> s_{a, x, c}) & (-s_{b, x, c} <-> s_{a, b, c}))")
        # a,b,c is a hole iff it has no points inside.
        Z.add_var(f'hole_{a, b, c}', description=f"{a, b, c} is a hole")
        x_range = list(range(a+1, b)) + list(range(b+1, c))
        for x in x_range:
            Z.constraint(f"inside_{x, a, b, c} -> -hole_{a, b, c}")
        Z.add_clause([f"hole_{triple}"] + [f"inside_{x, a, b, c}" for x in x_range])

    for triple in triples:
        Z.add_clause([f"-hole_{triple}"])
    return Z
        
encoding = encode(N)
encoding.serialize(f'{N}-points-wo-3-hole.cnf')
