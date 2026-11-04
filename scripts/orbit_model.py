"""Actions of slices and faces on the 24 coordinates of a generic inner orbit.

Coordinates are those of RubiksGN/Orbit.lean: k in Fin 24 stands for the sticker act k (-u, v, n).
Rows are x-slices at coordinate -u, columns are x-slices at coordinate +v.
"""
import sys
sys.path.insert(0,'scripts')
from rot import *

N,U,Vv=100,37,59         # any generic values: 0<u,v<n-1, u != v (same parity as n-1)
assert (U-(N-1))%2==0 and (Vv-(N-1))%2==0
BASE=(-U,Vv,N)
def clamp(t): return N-1 if t==N else (-(N-1) if t==-N else t)
AX={'x':0,'y':1,'z':2}
def slice_perm(ax,layer,d=1,base=BASE):
    """perm of Fin 24: k -> k' with move(act k base)=act k' base"""
    rot={'x':RX,'y':RY,'z':RZ}[ax]
    if d==-1: rot=INV[rot]
    out=[]
    for k in range(24):
        v=act(k,base)
        out.append(MUL[rot][k] if clamp(v[AX[ax]])==layer else k)
    return tuple(out)
def compose(a,b): return tuple(a[b[i]] for i in range(len(b)))   # a after b
def inverse(a):
    r=[0]*len(a)
    for i,x in enumerate(a): r[x]=i
    return tuple(r)
IDP=tuple(range(24))
def cycles(p):
    seen=set();res=[]
    for i in range(len(p)):
        if i in seen or p[i]==i: continue
        c=[i];seen.add(i);j=p[i]
        while j!=i: c.append(j);seen.add(j);j=p[j]
        res.append(tuple(c))
    return res
# on rep(u,v) : R = row u, K = col v ; Rm = row v (x=-v), Km = col u (x=+u)
R=slice_perm('x',-U); K=slice_perm('x',Vv); Rm=slice_perm('x',-Vv); Km=slice_perm('x',U)
FACES={'U':slice_perm('z',N-1),'D':slice_perm('z',-(N-1)),'F':slice_perm('y',N-1),'B':slice_perm('y',-(N-1)),
       'r':slice_perm('x',N-1),'l':slice_perm('x',-(N-1))}
if __name__=="__main__":
    print("R ",cycles(R)); print("K ",cycles(K)); print("Rm",cycles(Rm)); print("Km",cycles(Km))
    for f,p in FACES.items(): print(f,cycles(p))
    from sympy.combinatorics import Permutation,PermutationGroup
    pair=lambda a,b: Permutation(list(a)+[24+x for x in b])
    gens=[pair(FACES[f],FACES[f]) for f in FACES]+[pair(R,Rm)]
    G=PermutationGroup(gens); print("|<faces,(R,Rm)>| on 48 points =",G.order())
    import math
    print("  vs (24!)^2/2 =",math.factorial(24)**2//2)
    print("orbit single:",PermutationGroup([Permutation(list(FACES[f])) for f in FACES]+[Permutation(list(R))]).order(), math.factorial(24))
