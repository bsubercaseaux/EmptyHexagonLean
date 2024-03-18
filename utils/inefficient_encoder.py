from eznf import modeler # this is my library for encodings, it's similar to PySAT.
import itertools

N = 5 # number of points
k = 4 # gon-arity, (i.e., k = 4 means empty convex quadrilaterals).
# this encoding is good enough for getting SAT with N=9, k= 5 and UNSAT with N=10, k=5
# (note that in this case the mere encoding takes a few seconds, this is due to inefficiencies in my parsing code)

def encode(N, k):
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
        Z.constraint(f's_{a, b, c} or -s_{a, b, d} or s_{a, c, d}')
        Z.constraint(f'-s_{a, b, c} or s_{a, b, d} or -s_{a, c, d}')
        # 2
        Z.constraint(f's_{a, b, c} or -s_{a, c, d} or s_{b, c, d}')
        Z.constraint(f'-s_{a, b, c} or s_{a, c, d} or -s_{b, c, d}')
        # 3
        Z.constraint(f's_{a, b, c} or -s_{a, b, d} or s_{b, c, d}')
        Z.constraint(f'-s_{a, b, c} or s_{a, b, d} or -s_{b, c, d}')
        # 4
        Z.constraint(f's_{a, b, d} or -s_{a, c, d} or s_{b, c, d}')
        Z.constraint(f'-s_{a, b, d} or s_{a, c, d} or -s_{b, c, d}')

    # inside-ness variables
    for triple in triples:
        a, b, c = triple
        
      
        
        # we introduce hole variable to denote this triple being a hole
        Z.add_var(f"hole_{a, b, c}", f"{a, b, c} is an empty triangle")
        
        # given points are x-sorted, for x to be inside the abc triangle, we need a < x < c.
        # we also need to case on whether x < b or x > b
        for x in range(a + 1, b): # x < b
            Z.add_var(f'inside_{x, a, b, c}', description=f"{x} is inside the triangle {a, b, c}")
            
            # for x to be inside a, b, c, we need
            # s_{a, b, c} to have the same sign as s_{a, x, c}
            # and s_{a, x, b} to have the opposite sign to them.
            Z.constraint(f"inside_{x, a, b, c} <-> ((s_{a, b, c} <-> s_{a, x, c}) & (-s_{a, x, b} <-> s_{a, b, c}))")
            # this can be expressed with 6 clauses :) letting my library do the work for simplicity.
            
            
        for x in range(b+1,  c): # x > b
            Z.add_var(f'inside_{x, a, b, c}', description=f"{x} is inside the triangle {a, b, c}")
            
            # for x to be inside a, b, c, we need
            # s_{a, b, c} to have the same sign as s_{a, x, c}
            # and s_{b, x, c} to have the opposite sign to them.
            Z.constraint(f"inside_{x, a, b, c} <-> ((s_{a, b, c} <-> s_{a, x, c}) & (-s_{b, x, c} <-> s_{a, b, c}))")
        
        # a,b,c is a hole iff it has no points inside.
        for x in list(range(a+1, b)) + list(range(b+1, c)):
            Z.constraint(f"inside_{x, a, b, c} -> -hole_{a, b, c}") 
        Z.add_clause([f"hole_{a, b, c}"] + [f"inside_{x,a,b,c}" for x in list(range(a+1, b)) + list(range(b+1, c))])
        
        #  k points {p_1, p_2, ..., p_k} determine a convex k-hole
        #  if and only if all triangles p_a, p_b, p_c are holes for 1 <= a < b < c <= k
        #  
        # this is because "k points determine a convex k-hole <-> their convex hull has k points"
        #                                                     <-> all k points are in the convex hull"
        #                                                     <-> no point is inside a triangle from the set
        #                                                     <-> all triangles are holes
        
    k_tuples = list(itertools.combinations(range(N), k)) # this is only part that depends on k in this encoding.  
    for k_tuple in k_tuples:
        Z.add_var(f"convex_k_hole_{k_tuple}")
        Z.constraint(f"-convex_k_hole_{k_tuple}")
        # as we want to FORBID k-holes,
        # we need that for every k_tuple there is a non-empty triangle
        triangles = list(itertools.combinations(list(k_tuple), 3))
        Z.add_clause([f"convex_k_hole_{k_tuple}"] + [f"-hole_{a, b, c}" for a,b,c in triangles])
        for a,b,c in triangles:
            Z.add_clause([f"-convex_k_hole_{k_tuple}"] + [f"hole_{a, b, c}"])
    return Z
        
        
encoding = encode(N, k)
encoding.serialize(f'{N}-points-wo-{k}-hole.cnf')
