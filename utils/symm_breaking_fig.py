import math 


L_1 = [(-1.3, 0.25), (-1.3, 0.9), (-0.7, -0.45), (-0.35, 0.35), (-0.35, -0.8), (0.6, 0.5), (0.9, -0.6), (1.4, 1.1), (0.6, -1.1)]

def to_tikz(L):
    for i in range(len(L)):
        print(rf"\coordinate (c{i+1}) at {L[i]};")

    for i in range(len(L)):
        print(rf"\node[draw, circle, fill=blue, text=white, inner sep=0pt, minimum size=5pt] (p{i+1}) at {L[i]} {{\scriptsize ${i+1}$}};")


def rotate_by(p, theta):
    return (p[0]*math.cos(theta) - p[1]*math.sin(theta), p[0]*math.sin(theta) + p[1]*math.cos(theta))

def step_1(L):
    theta = 0.785398 
    def rot(p):
        return rotate_by(p, theta)
    return list(map(rot, L))

def trans_by(p, t):
    return (p[0]+t[0], p[1]+t[1])

def step_2(L):
    lmi = -1 
    lmx = 1e9
    for i in range(len(L)):
        if L[i][0] < lmx:
            lmx = L[i][0]
            lmi = i 
    t = (- L[lmi][0], -L[lmi][1])
    return [trans_by(p, t) for p in L]


def step_3(L):
    ans = []
    for p in L:
        if p[0] != 0:
            ans.append( (p[1]/p[0], 1/p[0]))
        else:
            ans.append( (-1.2, 3.85) )
    return ans

def step_4(L):
    return sorted(L, key=lambda p: p[0])

to_tikz(L_1)

no_same_x = step_1(L_1)
print('\nno same x:')
to_tikz(no_same_x)

translated = step_2(no_same_x)
print('\ntranslated:')
to_tikz(translated)

projected = step_3(translated)
print('\nprojected:')
to_tikz(projected)


sorted_pts = step_4(projected)
print('\nsorted:')
to_tikz(sorted_pts)

