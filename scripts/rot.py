"""Shared model: stickers are integer vectors, rotations are signed permutations."""
import itertools

def rotX(v): x,y,z=v; return (x,-z,y)
def rotXi(v): x,y,z=v; return (x,z,-y)
def rotY(v): x,y,z=v; return (z,y,-x)
def rotYi(v): x,y,z=v; return (-z,y,x)
def rotZ(v): x,y,z=v; return (-y,x,z)
def rotZi(v): x,y,z=v; return (y,-x,z)
ROT={('x',1):rotX,('x',-1):rotXi,('y',1):rotY,('y',-1):rotYi,('z',1):rotZ,('z',-1):rotZi}

GENERIC=(1,2,4)
def rotations():
    """the 24 proper signed permutations, identified by their image of a generic vector"""
    seen={GENERIC:()}; order=[GENERIC]; words=[()]
    i=0
    while i<len(order):
        v=order[i]; w=words[i]; i+=1
        for g in ('x','y','z'):
            u=ROT[(g,1)](v)
            if u not in seen:
                seen[u]=(g,)+w; order.append(u); words.append((g,)+w)
    assert len(order)==24
    return order,words
ORDER,WORDS=rotations()
IDX={v:i for i,v in enumerate(ORDER)}
def signed(i):
    """return (perm,signs) with act(i,v)[k]=signs[k]*v[perm[k]]"""
    im=ORDER[i]; perm=[];signs=[]
    for k in range(3):
        a=im[k]; perm.append({1:0,2:1,4:2}[abs(a)]); signs.append(1 if a>0 else -1)
    return perm,signs
def act(i,v):
    p,s=signed(i); return tuple(s[k]*v[p[k]] for k in range(3))
def mul(i,j): return IDX[act(i,ORDER[j])]   # act(mul i j)=act i ∘ act j
MUL=[[mul(i,j) for j in range(24)] for i in range(24)]
ID=IDX[GENERIC]
INV=[next(j for j in range(24) if MUL[i][j]==ID) for i in range(24)]
RX=IDX[rotX(GENERIC)];RY=IDX[rotY(GENERIC)];RZ=IDX[rotZ(GENERIC)]
RXi=INV[RX];RYi=INV[RY];RZi=INV[RZ]
