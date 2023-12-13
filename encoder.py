from eznf import modeler # this is my library for encodings, it's similar to PySAT.
import itertools

N = 5 # number of points

def encode(N):
    triples = list(itertools.combinations(range(N), 3)) # all possible ordered triples of points
    quadruples = list(itertools.combinations(range(N), 4)) # all possible ordered quadruples of points
    
    Z = modeler.Modeler() # create a modeler object, just the way of using my library
    
    for triple in triples:
        a, b, c = triple
        Z.add_var(f's_{a, b, c}', description=f"signotope of points {a}, {b}, {c}")
        
    # signotope axioms
    for quadruple in quadruples:
        a, b, c, d = quadruple
        # 1
        Z.add_clause(f's_{a, b, c} or -s_{a, b, d} or s_{a, c, d}')
        Z.add_clause(f'-s_{a, b, c} or s_{a, b, d} or -s_{a, c, d}')
        # 2
        Z.add_clause(f's_{a, b, c} or -s_{a, c, d} or s_{b, c, d}')
        Z.add_clause(f'-s_{a, b, c} or s_{a, c, d} or -s_{b, c, d}')
        # 3
        Z.add_clause(f's_{a, b, c} or -s_{a, b, d} or s_{b, c, d}')
        Z.add_clause(f'-s_{a, b, c} or s_{a, b, d} or -s_{b, c, d}')
        # 4
        Z.add_clause(f's_{a, b, d} or -s_{a, c, d} or s_{b, c, d}')
        Z.add_clause(f'-s_{a, b, d} or s_{a, c, d} or -s_{b, c, d}')

    # inside-ness variables
    for triple in triples:
        a, b, c = triple
        # given points are x-sorted, for x to be inside the abc triangle, we need a < x < c.
        # we also need to case on whether x < b or x > b
        for x in range(a + 1, b): # x < b
            Z.add_var(f'inside_{x, a, b, c}', description=f"{x} is inside the triangle {a, b, c}")
            
            # for x to be inside a, b, c, we need
            # s_{a, b, c} to have the same sign as s_{a, x, c}
            # and s_{a, x, b} to have the opposite sign to them.
            Z.add_clause(f"inside_{x, a, b, c} <-> ((s_{a, b, c} <-> s_{a, x, c}) & (-s_{a, x, b} <-> s_{a, b, c}))")
            # this can be expressed with 6 clauses :) letting my library do the work for simplicity.
            # inside_{x, a, b,c} -> C_1 & C_2
            # inside_{x, a, b, c} -> C_1
            # inside_{x, a, b, c} -> C_2
    return Z
        
        
encoding = encode(N)
encoding.serialize('4-hole-thm.cnf')