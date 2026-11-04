import sys,random,itertools; sys.path.insert(0,'scripts')
from rot import *
SHAPES={'pp':(RX,MUL[RX][RZi]),'pm':(RX,MUL[RXi][RZi]),'mp':(RXi,MUL[RX][RZi]),'mm':(RXi,MUL[RXi][RZi])}
def triples(shapes):
    T=set()
    for sh in shapes:
        A,B=SHAPES[sh]
        for t in range(24):
            c=(t,MUL[t][A],MUL[t][B]); assert len(set(c))==3
            T.add(c)
            T.add((c[0],c[2],c[1]))
    return T
def norm(c):
    m=min(range(3),key=lambda j:c[j]); return (c[m],c[(m+1)%3],c[(m+2)%3])
for shapes in (['pp'],['pp','mp'],['pp','pm'],['pp','mm'],['pp','pm','mp','mm']):
    T={norm(c) for c in triples(shapes)}
    F={frozenset(c) for c in T}
    print(shapes,len(T),"directed;",len(F),"unordered triples")
    # greedy elimination: remove a point keeping the rest connected as long as possible
    random.seed(0)
    best=0
    for trial in range(20000):
        rem=set(range(24));order=[]
        while len(rem)>2:
            cands=list(rem);random.shuffle(cands);ok=False
            for b in cands:
                # connectivity of rem (root b): every point reachable by triples inside rem
                TT=[c for c in F if c<=rem]
                seen={b};ch=True
                while ch:
                    ch=False
                    for c in TT:
                        if c&seen and not c<=seen: seen|=c;ch=True
                if seen==rem:
                    order.append(b);rem=rem-{b};ok=True;break
            if not ok:break
        if len(order)>best:
            best=len(order);print("  levels",best,"rem",len(rem),"order",order[:best] if best==22 else "")
        if best==22:break
