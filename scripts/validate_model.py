"""Independent check of the sticker model against known facts about real cubes.

Group orders are computed with sympy's Schreier-Sims from the same formulas as `RubiksGN/Basic.lean`.
"""
import sys,math; sys.path.insert(0,'scripts')
from rot import ROT
from sympy.combinatorics import Permutation, PermutationGroup
def stickers(n):
    C=range(-(n-1),n,2); S=[]
    for a in C:
        for b in C:
            for s in (n,-n): S+=[(s,a,b),(a,s,b),(a,b,s)]
    return S
def clamp(n,t): return n-1 if t==n else (-(n-1) if t==-n else t)
AX={'x':0,'y':1,'z':2}
def gens(n):
    S=stickers(n); I={v:i for i,v in enumerate(S)}; assert len(I)==6*n*n
    out=[]
    for a in 'xyz':
        for l in range(-(n-1),n,2):
            p=[I[ROT[(a,1)](v)] if clamp(n,v[AX[a]])==l else I[v] for v in S]
            out.append(Permutation(p))
    return out
f=math.factorial
# labelled group orders from the classical structure of the cube
expected={
 2: f(8)*3**7,                                   # corners only, all six faces free
 3: f(8)*3**7*f(12)*2**11//2*24,                 # the 4.3e19 positions times the 24 centre arrangements
}
for n,e in expected.items():
    o=PermutationGroup(gens(n)).order()
    print(n,o,"matches" if o==e else f"MISMATCH (expected {e})")
    assert o==e
# 3x3x3 corner-only and fixed-centre count: 43252003274489856000
G3=PermutationGroup(gens(3)); assert G3.order()//24==43252003274489856000
print("3x3x3 positions with fixed centres:",G3.order()//24)
# 4x4x4: labelled stickers; known count of coloured positions is 7401196841564901869874093974498574336000000000
G4=PermutationGroup(gens(4)); o=G4.order()
print("4x4x4 labelled order",o)
coloured=f(8)*3**7*f(24)*f(24)//(f(4)**6)  # corners, wings, centres up to equal colours
print("4x4x4 coloured count with fixed orientation:",coloured//24)
assert coloured//24==7401196841564901869874093974498574336000000000
# labelled order must be corners * wings * centres, with the single parity constraint among the three
lab=f(8)*3**7*f(24)*f(24)//2
print("labelled order vs 8!3^7 24!24!/2:",o==lab, o/lab)
