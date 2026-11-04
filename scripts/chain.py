import sys,random,itertools,json,time; sys.path.insert(0,'scripts')
from skel import *
def pinv(p):
    r=[0]*len(p)
    for i,x in enumerate(p): r[x]=i
    return tuple(r)
def conj_pool(seeds,setups,P,N,other):
    pool={}
    for w in seeds:
        for s in setups:
            u=tuple(s)+tuple(w)+inv(s)
            p=ev(u,P,N)
            if p==tuple(range(N)):continue
            if p not in pool or len(u)<len(pool[p]): pool[p]=u
    return pool
def setups(moves,k):
    out=[()]
    for l in range(1,k+1):
        out+=list(itertools.product(moves,repeat=l))
    return out
def build(pool,P,N,order=None,prefer=None):
    """stabilizer chain; each level (base, {pt:(perm,word)}) from identity"""
    idp=tuple(range(N)); levels=[]
    fixed=[]
    pool=dict(pool)
    points=order or list(range(N))
    for b in points:
        cur={p:w for p,w in pool.items()}
        if all(p[b]==b for p in cur):
            continue
        # BFS over pool with shortest words (Dijkstra by length)
        import heapq
        T={b:(idp,())}; h=[(0,b)]
        seen={}
        gens=sorted(cur.items(),key=lambda kv:len(kv[1]))
        while h:
            d,x=heapq.heappop(h)
            if d>len(T[x][1]):continue
            for p,w in gens:
                y=p[x]
                nw=tuple(w)+T[x][1]
                if y not in T or len(nw)<len(T[y][1]):
                    T[y]=(comp(p,T[x][0]),nw); heapq.heappush(h,(len(nw),y))
        levels.append((b,T))
        # next pool: elements fixing b, plus Schreier residuals
        nxt={p:w for p,w in cur.items() if p[b]==b}
        for p,w in gens[:400]:
            for x,(tp,tw) in T.items():
                y=p[x]; up,uw=T[y]
                res=comp(pinv(up),comp(p,tp))
                if res==idp: continue
                assert res[b]==b
                rw=inv(uw)+tuple(w)+tw
                if res not in nxt or len(rw)<len(nxt[res]): nxt[res]=rw
        # keep shortest many
        items=sorted(nxt.items(),key=lambda kv:len(kv[1]))[:3000]
        pool=dict(items)
    return levels
def sift(levels,g,idp,startlevel=0):
    """returns list of (level,pt) or None"""
    out=[]
    for k in range(startlevel,len(levels)):
        b,T=levels[k]
        x=g[b]
        if x not in T:return None
        tp,tw=T[x]
        g=comp(pinv(tp),g); out.append((k,x))
    return out if g==idp else None
def check(levels,N,gensExtra):
    idp=tuple(range(N)); count=0
    allT=[]
    for k in reversed(range(len(levels))):
        b,T=levels[k]
        S=[tp for lv in levels[k:] for (_,(tp,_)) in lv[1].items()]
        if k==0:S=S+list(gensExtra)
        for s in S:
            for x,(tp,_) in T.items():
                g=comp(s,tp); count+=1
                if sift(levels,g,idp,k) is None: return False,count
    return True,count
if __name__=="__main__":
    t=time.time()
    # ---- corners
    cseed=[(('x',-2,1),('y',-2,1),('x',-2,-1),('y',2,1),('x',-2,1),('y',-2,-1),('x',-2,-1),('y',2,-1))]
    assert desc(cseed[0])==(9,0,0)
    cpool=conj_pool(cseed,setups(OUTS,3),CP,24,None)
    print("corner pool",len(cpool),time.time()-t)
    cl=build(cpool,CP,24)
    print("corner levels",[len(T) for b,T in cl],"max word per level",[max(len(v[1]) for v in T.values()) for b,T in cl])
    print("total word bound",sum(max(len(v[1]) for v in T.values()) for b,T in cl))
    L=[CP[m] for m in SYM if m[1]!=0]
    idp=tuple(range(24))
    def closed(L,levels,N):
        idp=tuple(range(N)); bad=0
        for s in L:
            if sift(levels,comp(s,s),idp) is None:bad+=1
            for t in L:
                if sift(levels,comp(comp(s,t),comp(pinv(s),pinv(t))),idp) is None: bad+=1
        return bad
    print("corner sq/comm failures",closed(L,cl,24))
    print("corner closure",check(cl,24,[]),time.time()-t)
    json.dump([[b,{str(k):v[1] for k,v in T.items()}] for b,T in cl],open('/tmp/claude-1000/corner.json','w')) if False else None
    # ---- edges
    eseed=[(('x',0,1),('y',-2,1),('y',-2,1),('x',0,-1),('y',-2,-1),('y',-2,-1))]
    assert desc(eseed[0])==(0,6,0)
    epool=conj_pool(eseed,setups(SYM,3),EP,24,None)
    print("edge pool",len(epool),time.time()-t)
    el=build(epool,EP,24)
    print("edge levels",[len(T) for b,T in el],"max word per level",[max(len(v[1]) for v in T.values()) for b,T in el])
    print("total word bound",sum(max(len(v[1]) for v in T.values()) for b,T in el))
    LE=[EP[m] for m in SYM]
    print("edge sq/comm failures",closed(LE,el,24))
    # conj closure
    badc=0
    for s in LE:
        for lv in el:
            for x,(tp,_) in lv[1].items():
                if sift(el,comp(comp(s,tp),pinv(s)),idp) is None: badc+=1
    print("edge conj failures",badc)
    print("edge closure",check(el,24,[]),time.time()-t)
    # purity
    for lv in el:
        for x,(tp,w) in lv[1].items():
            assert ev(w,CP,24)==idp and ev(w,FP,6)==tuple(range(6)) and even(w)
    for lv in cl:
        for x,(tp,w) in lv[1].items():
            assert ev(w,EP,24)==idp and ev(w,FP,6)==tuple(range(6)) and even(w)
    print("purity ok")
    # ---- centres: mid-slice commutators with the edge part removed
    def edge_cancel(w):
        g=ev(w,EP,24)
        out=sift(el,g,idp)
        assert out is not None
        res=()
        for (k,x) in out:
            res=res+el[k][1][x][1]
        return inv(res)+tuple(w)
    seedsZ=[commw((('x',0,1),),(('y',0,1),)),commw((('y',0,1),),(('z',0,1),)),commw((('z',0,1),),(('x',0,1),)),
            commw((('x',0,1),('x',0,1)),(('y',0,1),('y',0,1))) ]
    zp={}
    for w in seedsZ+[inv(s) for s in seedsZ]:
        u=edge_cancel(w)
        assert ev(u,EP,24)==idp and ev(u,CP,24)==idp and even(u),(desc(u))
        zp[ev(u,FP,6)]=u
    print("centre seeds",{len(v) for v in zp.values()},len(zp))
    zl=build(zp,FP,6)
    print("centre levels",[len(T) for b,T in zl],"max word",[max(len(v[1]) for v in T.values()) for b,T in zl])
    LZ=[FP[m] for m in SYM]
    print("centre sq/comm",closed(LZ,zl,6),"closure",check(zl,6,[]))
    bad=0
    for s in LZ:
        for lv in zl:
            for x,(tp,_) in lv[1].items():
                if sift(zl,comp(comp(s,tp),pinv(s)),tuple(range(6))) is None: bad+=1
    print("centre conj failures",bad)
    # corner conj
    bad=0
    for s in L:
        for lv in cl:
            for x,(tp,_) in lv[1].items():
                if sift(cl,comp(comp(s,tp),pinv(s)),idp) is None: bad+=1
    print("corner conj failures",bad)
    import pickle
    pickle.dump((cl,el,zl),open('scripts/chains.pkl','wb'))
    print(time.time()-t)
