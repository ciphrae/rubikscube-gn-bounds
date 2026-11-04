"""Skeleton (corner / edge / face-centre) chains on the 3x3x3 model with all-even pure words."""
import sys,random,itertools,json; sys.path.insert(0,'scripts')
from rot import *
n=3
AX={'x':0,'y':1,'z':2}
def clamp(t): return n-1 if t==n else (-(n-1) if t==-n else t)
VC=(-2,2,3);VE=(-2,0,3)
FACES=[(0,0,3),(0,0,-3),(0,3,0),(0,-3,0),(3,0,0),(-3,0,0)]
# symbolic quarter move: (axis, layer in {-2,0,2}, dir)
SYM=[(a,l,d) for a in 'xyz' for l in (-2,0,2) for d in (1,-1)]
def mv(m,v):
    a,l,d=m
    return ROT[(a,d)](v) if clamp(v[AX[a]])==l else v
CI={act(i,VC):i for i in range(24)};EI={act(i,VE):i for i in range(24)};FI={f:i for i,f in enumerate(FACES)}
assert len(CI)==24 and len(EI)==24
CP={m:tuple(CI[mv(m,act(i,VC))] for i in range(24)) for m in SYM}
EP={m:tuple(EI[mv(m,act(i,VE))] for i in range(24)) for m in SYM}
FP={m:tuple(FI[mv(m,f)] for f in FACES) for m in SYM}
def comp(p,q): return tuple(p[i] for i in q)  # (p*q)(i)=p(q(i))
def ev(w,P,N):
    r=tuple(range(N))
    for m in w: r=comp(r,P[m])
    return r
def inv(w): return tuple((a,l,-d) for (a,l,d) in reversed(w))
def state(w): return (ev(w,CP,24),ev(w,EP,24),ev(w,FP,6))
IDs=(tuple(range(24)),tuple(range(24)),tuple(range(6)))
def even(w):
    from collections import Counter
    c=Counter((a,l) for a,l,d in w); return all(v%2==0 for v in c.values())
def commw(a,b): return tuple(a)+tuple(b)+inv(a)+inv(b)
def nm(s):
    # singmaster-ish: U=z+2 , D=z-2, R=x+2, L=x-2, B=y+2, F=y-2, M=x0,S=y0,E=z0
    return s
R=('x',2,1);L=('x',-2,1);U=('z',2,1);D=('z',-2,1);B=('y',2,1);F=('y',-2,1);M=('x',0,1);S=('y',0,1);E=('z',0,1)
def i1(m): return (m[0],m[1],-m[2])
OUT=[R,L,U,D,B,F]
OUTS=[m for m in SYM if m[1]!=0]
MIDS=[m for m in SYM if m[1]==0]
def desc(w):
    s=state(w)
    return (sum(1 for i in range(24) if s[0][i]!=i),sum(1 for i in range(24) if s[1][i]!=i),sum(1 for i in range(6) if s[2][i]!=i))
if __name__=="__main__":
    # search pure seeds among commutators
    seeds={}
    import collections
    words1=[(m,) for m in SYM]
    words2=[(a,b) for a in SYM for b in SYM]
    words3=[(a,b,c) for a in SYM for b in SYM for c in SYM]
    best={}
    for A in words3:
        if any(m[1]==0 for m in A):continue
        for b in words1+words2:
            if any(m[1]==0 for m in b):continue
            w=commw(A,b)
            d=desc(w)
            if d[0]>0 and d[1]==0 and d[2]==0:
                if d[0] not in best or len(w)<len(best[d[0]]):
                    best[d[0]]=w
    print("pure corner seeds (moved stickers->len):",{k:len(v) for k,v in best.items()})
    print(best)
    bestE={}
    for A in words1+words2:
        for b in words1+words2:
            w=commw(A,b)
            d=desc(w)
            if d[0]==0 and d[1]>0 and d[2]==0:
                if d[1] not in bestE or len(w)<len(bestE[d[1]]):
                    bestE[d[1]]=w
    print("pure edge seeds:",{k:len(v) for k,v in bestE.items()})
    print(bestE)
