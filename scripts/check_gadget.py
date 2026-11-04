"""Brute-force check of the rectangle gadget on actual cubes."""
import sys; sys.path.insert(0,'scripts')
from rot import *
import random
def coords(n): return list(range(-(n-1),n,2))
def stickers(n):
    C=coords(n);S=[]
    for a in C:
        for b in C:
            for s in (n,-n):
                S+= [(s,a,b),(a,s,b),(a,b,s)]
    return S
def clamp(n,t): return n-1 if t==n else (-(n-1) if t==-n else t)
AX={'x':0,'y':1,'z':2}
def move(n,ax,layers,d,v):
    return ROT[(ax,d)](v) if clamp(n,v[AX[ax]]) in layers else v
def gadget(n,X,Y,v,tau=ID,inv=False):
    """c=a b a^-1 b^-1 with a=rotX on X, b=U (rotX on Y) U^-1 ; conjugated by tau (applied right to left)"""
    v=act(INV[tau],v)
    a =lambda w:move(n,'x',X,1,w); ai=lambda w:move(n,'x',X,-1,w)
    U =lambda w:move(n,'z',{n-1},1,w); Ui=lambda w:move(n,'z',{n-1},-1,w)
    B =lambda w:move(n,'x',Y,1,w); Bi=lambda w:move(n,'x',Y,-1,w)
    b =lambda w:U(B(Ui(w))); bi=lambda w:U(Bi(Ui(w)))
    v=a(b(ai(bi(v))))
    return act(tau,v)
ALPHA=RX; BETA=MUL[RX][RZi]
for n in (4,5,6,7,8,9,10):
    S=stickers(n); assert len(set(S))==6*n*n
    R=[c for c in coords(n) if -(n-1)<c<0]
    Cl=[c for c in coords(n) if 0<=c<n-1]+[n-1]
    for trial in range(40):
        X=set(random.sample(R,random.randint(1,len(R))))
        Y=set(random.sample(Cl,random.randint(1,len(Cl))))
        tau=random.randrange(24)
        moved={v:gadget(n,X,Y,v,tau) for v in S if gadget(n,X,Y,v,tau)!=v}
        exp={}
        for x in X:
            for y in Y:
                p=(x,y,n)
                def e(i): return act(i,p)
                t0,t1,t2=tau,MUL[tau][ALPHA],MUL[tau][BETA]
                exp[e(t0)]=e(t1);exp[e(t1)]=e(t2);exp[e(t2)]=e(t0)
                if y==n-1:
                    q=(x,n,n-1)
                    def e2(i): return act(i,q)
                    exp[e2(t0)]=e2(t1);exp[e2(t1)]=e2(t2);exp[e2(t2)]=e2(t0)
        assert moved==exp,(n,X,Y,tau)
print("gadget formula verified: exact 3-cycles, nothing else moves")
