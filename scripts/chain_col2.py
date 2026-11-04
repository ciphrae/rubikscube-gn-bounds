"""Coloured round scheme: template lists whose levels are *regular* for the colouring goal.

Run `uv run python scripts/chain_col2.py` to rebuild scripts/chain_col2.json (a few minutes, one core) and
`uv run python scripts/check_chain_col2.py` to verify it independently.
`--exact-search N seconds seed m1 m2 ...` runs the bounded annealing for an exact factorization of the 4-subsets of N points.

Conventions: those of RubiksGN/PassAction.lean, permutations are tuples, (a*b)(k) = a[b[k]].
Common coordinates: mirror raw coordinate = PHI(common coordinate); L = PHI^-1 colM PHI; kc o PHI = kc.

Goal on one orbit, with pi the action of the scramble and R the action of the program: R * pi in Y = {s : kc o s = kc}.
So R must hit every RIGHT coset Y x. Time order of a family: x_1 first, R = x_N ... x_1. Family O (rows in the second pass):
x = eT t = c K^-1. Family E (rows in the first pass): x = K c^-1 = (eT t)^-1. A level places a base position b:
  for every unplaced position p there is exactly one entry with x(p) = b, and every x fixes the placed positions.
The position p to bring to b has to hold the colour kc(b), and the unplaced positions holding that colour number exactly
w = 4 - #{placed positions of colour kc(b)}, whatever the state. So every state has exactly w good entries in a list of m.
Sum over a whole orbit of log2(m/w), plus log2 60 for the last five points, is exactly log2 Z.
"""
import itertools
import json
import math
import os
import random
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rot import MUL, RX, RY, RZ, act

ID = tuple(range(24))
VG = (-1, 2, 3)
AX = {'x': (0, RX), 'y': (1, RY), 'z': (2, RZ)}
OUT = os.path.join(HERE, 'chain_col2.json')


def gen_p(a, c):
    i, r = AX[a]
    return tuple(MUL[r][k] if act(k, VG)[i] == c else k for k in range(24))


def comp(a, b):
    return tuple(a[x] for x in b)


def inv(a):
    r = [0] * len(a)
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)


def dpow(d, g):
    return g if d else inv(g)


def cycle_of(p):
    i = next(k for k in range(24) if p[k] != k)
    c = [i]
    while p[c[-1]] != i:
        c.append(p[c[-1]])
    return tuple(c)


def perm_of(c):
    p = list(range(24))
    for i, x in enumerate(c):
        p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def canon(c):
    i = c.index(min(c))
    return tuple(c[(i + j) % 4] for j in range(4))


def mask(c):
    m = 0
    for x in c:
        m |= 1 << x
    return m


LETTERS = [(a, s, d) for a in 'xyz' for s in (True, False) for d in (True, False)]
FACE = {l: dpow(l[2], gen_p(l[0], 3 if l[1] else -3)) for l in LETTERS}
ROWT = {l: dpow(l[2], gen_p(l[0], 1 if l[1] else -1)) for l in LETTERS}
ROWM = {l: dpow(l[2], gen_p(l[0], 2 if l[1] else -2)) for l in LETTERS}
COLK = gen_p('x', 2)
COLM = gen_p('x', 1)
KC = canon(cycle_of(COLK))
LP = gen_p('x', -2)
LC = canon(cycle_of(LP))
_loc = {act(k, (-2, 1, 3)): k for k in range(24)}
PHI = tuple(_loc[tuple(-t if abs(t) == 2 else t for t in act(k, VG))] for k in range(24))
PHI_I = inv(PHI)
assert comp(PHI_I, comp(COLM, PHI)) == LP
FACE_VEC = (0, 0, 3)


def face_of_vec(v):
    return 0 if v[2] == 3 else 1 if v[2] == -3 else 2 if v[1] == 3 else 3 if v[1] == -3 else 4 if v[0] == 3 else 5


KCOL = tuple(face_of_vec(act(k, VG)) for k in range(24))
assert all(KCOL[PHI[k]] == KCOL[k] for k in range(24))


def build_pieces():
    block = {}
    for a, s in itertools.product('xyz', (True, False)):
        for x in cycle_of(FACE[(a, s, True)]):
            block[x] = (a, s)
    out = {}
    for rk, r in ROWT.items():
        bls = [block[x] for x in cycle_of(r)]
        for rs in itertools.product((0, 1, -1, 2), repeat=4):
            word = []
            for (a, s), t in zip(bls, rs):
                word += [(a, s, t > 0)] * abs(t)
            f = ID
            for w in word:
                f = comp(f, FACE[w])
            cj = comp(comp(f, r), inv(f))
            cost = 2 * len(word) + 1
            if cj not in out or out[cj][0] > cost:
                out[cj] = (cost, word, rk)
    return out


def build_ball(pieces, limit):
    """shortest words for the pairs of cycles (hKh^-1, hLh^-1), the new piece on the left"""
    pl = sorted(((v[0], p) for p, v in pieces.items()), key=lambda t: (t[0], t[1]))
    start = (KC, LC)
    dist = {start: (0, None, None)}
    buckets = [[] for _ in range(limit + 1)]
    buckets[0].append(start)
    for w in range(limit + 1):
        for s in buckets[w]:
            if dist[s][0] != w:
                continue
            for pc, p in pl:
                if w + pc > limit:
                    break
                ns = (canon(tuple(p[x] for x in s[0])), canon(tuple(p[x] for x in s[1])))
                o = dist.get(ns)
                if o is None or o[0] > w + pc:
                    dist[ns] = (w + pc, s, p)
                    buckets[w + pc].append(ns)
    return dist


class Search:
    def __init__(self, limit):
        self.limit = limit
        self.pieces = build_pieces()
        self.dist = build_ball(self.pieces, limit)
        print('ball', len(self.dist), flush=True)
        ordered = sorted(self.dist.items(), key=lambda kv: (kv[1][0], kv[0]))
        self.arc = {'T': {}, 'M': {}}
        self.late = {'T': {}, 'M': {}}
        for s, v in ordered:
            rec = (v[0], mask(s[0]), mask(s[1]), s)
            for i in range(4):
                self.arc['T'].setdefault((s[0][i], s[0][(i + 1) % 4]), []).append(rec)
                self.arc['M'].setdefault((s[1][i], s[1][(i + 1) % 4]), []).append(rec)
                if s[1] == LC:
                    self.late['T'].setdefault((s[0][i], s[0][(i + 1) % 4]), []).append(rec)
                if s[0] == KC:
                    self.late['M'].setdefault((s[1][i], s[1][(i + 1) % 4]), []).append(rec)
        self.memo = {}

    def arc_of(self, fam, kind, b, x):
        """the arc the free cycle needs so that the element sends position x to base b"""
        plain = COLK if kind == 'T' else LP
        if fam == 'O':      # x = c P^-1: c(P^-1 x) = b
            return (inv(plain)[x], b)
        return (b, x)       # x = P c^-1, P fixes b: c^-1 x = b

    def pick(self, fam, kind, late, b, x, f, p):
        tab = self.late[kind] if late else self.arc[kind]
        for rec in tab.get(self.arc_of(fam, kind, b, x), ()):
            if rec[1] & f == 0 and rec[2] & p == 0:
                return rec
        return None

    def level(self, fam, kind, late, b, f, p):
        key = (fam, kind, late, b, f, p)
        if key in self.memo:
            return self.memo[key]
        placed = f if kind == 'T' else p
        mx = tot = 0
        for x in range(24):
            if placed >> x & 1 or x == b:
                continue
            rec = self.pick(fam, kind, late, b, x, f, p)
            if rec is None:
                mx, tot = 99, 10 ** 6
                break
            mx, tot = max(mx, rec[0]), tot + rec[0]
        self.memo[key] = (mx, tot)
        return mx, tot

    def early(self, fam, om_t, om_m):
        """best alternating order T1,M1,...,T5,M5: the target places om_m, the mirror places om_t"""
        memo = {}

        def go(f, p, turn):
            if bin(f).count('1') == 5 and bin(p).count('1') == 5:
                return (0, ())
            key = (f, p, turn)
            if key in memo:
                return memo[key]
            best = None
            pool, placed = (om_m, f) if turn == 'T' else (om_t, p)
            for b in pool:
                if placed >> b & 1:
                    continue
                mx, t = self.level(fam, turn, False, b, f, p)
                if mx > self.limit:
                    continue
                r = go(f | 1 << b, p, 'M') if turn == 'T' else go(f, p | 1 << b, 'T')
                if r is not None and (best is None or r[0] + t < best[0]):
                    best = (r[0] + t, ((turn, b),) + r[1])
            memo[key] = best
            return best
        return go(0, 0, 'T')

    def late_order(self, fam, kind, z, f0, p0, rng, tries=200):
        best = None
        pts = list(z)
        for _ in range(tries):
            rng.shuffle(pts)
            f, p = f0, p0
            tot = 0
            ok = True
            for b in pts:
                mx, t = self.level(fam, kind, True, b, f, p)
                if mx > self.limit:
                    ok = False
                    break
                tot += t
                if kind == 'T':
                    f |= 1 << b
                else:
                    p |= 1 << b
            if ok and (best is None or tot < best[0]):
                best = (tot, tuple(pts))
        return best

    def factorization(self, base, kind, e, a=5, b=12):
        """least total cost X, Y with X*Y = Alt(base + e), both lists of elements c P^-1 with the other element 1"""
        om = list(base) + [e]
        bi = inv(perm_of(base))
        cost = {}
        for t in itertools.permutations(om, 4):
            if t[0] == min(t):
                s = (t, LC) if kind == 'T' else (KC, t)
                if s in self.dist:
                    cost[t] = self.dist[s][0]
        cs = sorted(cost)
        els = [comp(perm_of(c), bi) for c in cs]
        ids = {}
        n = len(els)
        m = [[ids.setdefault(comp(els[i], els[j]), len(ids)) for j in range(n)] for i in range(n)]
        w = [cost[c] for c in cs]
        sw = sorted(w)
        best = None
        full = (1 << 60) - 1
        for x in itertools.combinations(range(n), a):
            sx = sum(w[i] for i in x)
            if best is not None and sx + sum(sw[:b]) >= best[0]:
                continue
            fps = []
            for j in range(n):
                fp = 0
                for i in x:
                    if fp >> m[i][j] & 1:
                        fp = None
                        break
                    fp |= 1 << m[i][j]
                if fp is not None:
                    fps.append((w[j], fp, j))
            if len(fps) < b:
                continue
            uni = 0
            for _, fp, _j in fps:
                uni |= fp
            if uni != full:
                continue
            fps.sort()
            by = {}
            for t in fps:
                ff = t[1]
                while ff:
                    low = ff & -ff
                    by.setdefault(low, []).append(t)
                    ff ^= low

            def rec(cov, sol, s):
                nonlocal best
                if len(sol) == b:
                    if best is None or sx + s < best[0]:
                        best = (sx + s, x, tuple(sol))
                    return
                if best is not None and sx + s + (b - len(sol)) * sw[0] >= best[0]:
                    return
                rem = full & ~cov
                low = rem & -rem
                for wj, fp, j in by.get(low, ()):
                    if not fp & cov:
                        rec(cov | fp, sol + [j], s + wj)
            rec(0, [], 0)
        if best is None:
            return None
        return best[0], [cs[i] for i in best[1]], [cs[j] for j in best[2]]

    def template(self, s):
        out = []
        while self.dist[s][1] is not None:
            _, parent, p = self.dist[s]
            _, word, rk = self.pieces[p]
            out.append((word, rk))
            s = parent
        return out


EXACT_SEARCH = {
    'question': 'exact factorization: lists of 4-cycles with product of sizes C(N,4), every 4-subset sent to one set by exactly one product',
    'found': {'N': 8, 'first_applied': [[3, 1, 6, 5], [2, 6, 3, 5], [2, 3, 6, 1], [5, 6, 2, 1], [2, 5, 1, 3]],
              'second_applied': [[5, 2, 4, 0], [1, 7, 4, 6], [1, 5, 7, 2], [5, 1, 6, 0], [6, 2, 7, 1], [0, 2, 7, 1], [2, 1, 4, 0],
                                 [7, 1, 0, 4], [1, 5, 4, 0], [1, 2, 4, 3], [5, 0, 1, 3], [0, 3, 1, 5], [4, 0, 6, 7], [3, 7, 4, 0]],
              'target_set': [1, 2, 3, 4]},
    'annealing_best_uncovered_at_exact_sizes': {'N=9 (126)': 7, 'N=10 (210)': 5, 'N=12 (495)': 59, 'N=16 (1820)': 290, 'N=24 (10626)': 2236},
    'effort': 'about 120 s per size pattern on one core, 2 and 3 lists, 38 patterns; no exhaustive result; unresolved for N >= 9',
    'needed': False,
}


def tmpl_json(t):
    return [[[list(l) for l in f], list(r)] for f, r in t]


def tmpl_len(t):
    return sum(2 * len(f) + 1 for f, _ in t)


def eval_on(t, rows):
    h = ID
    for f, r in t:
        fv = ID
        for w in f:
            fv = comp(fv, FACE[w])
        h = comp(h, comp(comp(fv, rows[r]), inv(fv)))
    return h


def entry(srch, s, fam):
    t = srch.template(s)
    h, hm = eval_on(t, ROWT), eval_on(t, ROWM)
    assert canon(cycle_of(comp(comp(h, COLK), inv(h)))) == s[0]
    assert canon(cycle_of(comp(comp(hm, COLM), inv(hm)))) == canon(tuple(PHI[x] for x in s[1]))
    return tmpl_json(t), tmpl_len(t)


def build_family(srch, fam, e_t, e_m, finals, rng):
    om_t = KC + (e_t,)
    om_m = LC + (e_m,)
    z = [x for x in range(24) if x not in om_t + om_m]
    early = srch.early(fam, om_t, om_m)
    assert early, 'no early order'
    f, p = 0, 0
    steps = []
    for kind, b in early[1]:
        steps.append((kind, False, b))
    fm = mask(om_m)
    pm = mask(om_t)
    lt = srch.late_order(fam, 'T', z, fm, pm, rng)
    lm = srch.late_order(fam, 'M', z, fm, pm, rng)
    assert lt and lm, 'no late order'
    steps += [('T', True, b) for b in lt[1]] + [('M', True, b) for b in lm[1]]
    levels = []
    for kind, late, b in steps:
        ents = []
        for x in range(24):
            if (f if kind == 'T' else p) >> x & 1:
                continue
            if x == b:
                s = (KC, LC)
            else:
                s = srch.pick(fam, kind, late, b, x, f, p)[3]
            tj, ln = entry(srch, s, fam)
            raw_x = x if kind == 'T' else PHI[x]
            ents.append({'position': raw_x, 'template': tj})
        placed = f if kind == 'T' else p
        w = 4 - sum(1 for y in range(24) if placed >> y & 1 and KCOL[y] == KCOL[b])
        levels.append({'orbit': kind, 'kind': 'place', 'base': b if kind == 'T' else PHI[b], 'w': w, 'entries': ents})
        if kind == 'T':
            f |= 1 << b
        else:
            p |= 1 << b
    # final levels: X*Y = Alt(Omega) in eT; O plays Y then X, E plays the inverses of X then of Y
    for kind in 'TM':
        fx, fy = finals[kind]
        for lst, nm in ((fy, 'Y'), (fx, 'X')) if fam == 'O' else ((fx, 'X'), (fy, 'Y')):
            ents = []
            for c in lst:
                s = (c, LC) if kind == 'T' else (KC, c)
                tj, ln = entry(srch, s, fam)
                ents.append({'template': tj})
            levels.append({'orbit': kind, 'kind': 'final' + nm, 'w': 1, 'entries': ents})
    return levels


def lean_lists(levels, fam):
    """the list of lists for Lean: O reversed time, E in time order"""
    return list(reversed(range(len(levels)))) if fam == 'O' else list(range(len(levels)))


def greedy_code(m, w, s, rng):
    """greedy hitting set of all boxes W_1 x ... x W_s, |W_i| = w, in {0..m-1}^s. Tiny parameters only."""
    subs = list(itertools.combinations(range(m), w))
    masks = [sum(1 << x for x in c) for c in subs]
    words = list(itertools.product(range(m), repeat=s))
    boxes = set(itertools.product(range(len(subs)), repeat=s))
    code = []
    while boxes:
        best, gain = None, -1
        for wd in rng.sample(words, min(len(words), 400)):
            g = sum(all(masks[b[i]] >> wd[i] & 1 for i in range(s)) for b in boxes)
            if g > gain:
                best, gain = wd, g
        code.append(best)
        boxes = {b for b in boxes if not all(masks[b[i]] >> best[i] & 1 for i in range(s))}
    return code


def finite_table(levels_mw, L=8):
    """W(n) log2 n / n^2 from exactW, with the best S and slot budget: rounds R = Sum (S/2/s + 1), Cslot = |C| 2 s L, gadget 2200 r S.
    Normalised terms, r = n/2: main A ln/8, slots A Cslot ln/(4r), rounding + gadget 2 ln sqrt(K 550/(2r)) with K levels, where A = Sum 1/s, ln = log2 n."""
    plain = [(m, 1) for m in (83, 228, 56, 149, 33, 89, 18, 40, 7, 10)] * 2
    out = {}
    for ex in (6, 12, 30, 100, 300, 1000):
        ln = ex * math.log2(10)
        lr = ln - 1
        row = {}
        for name, mw in (('regular_with_codes', levels_mw), ('plain_lists_prefix', plain)):
            best = None
            for b in [max(4.0, lr - x / 2) for x in range(0, 120)]:
                ss = []
                for m, w in mw:
                    r = math.log2(m / w)
                    s = int(b / r)
                    while s > 0 and w > 1 and s * r + math.log2(1 + s * math.log(math.comb(m, w))) > b:
                        s -= 1
                    ss.append(s)
                if min(ss) == 0:
                    continue
                a = sum(1 / q for q in ss)
                logc = b + math.log2(2 * max(ss) * L)
                if logc - lr > 0:
                    continue
                tot = a * ln / 8 + a * 2 ** (logc - lr) * ln / 4 + 2 * ln * 2 ** (0.5 * (math.log2(len(mw) * 550 / 2) - lr))
                if best is None or tot < best[0]:
                    best = (tot, b)
            row[name] = {'ratio': best[0], 'log2_slots': best[1]} if best else None
        out['1e%d' % ex] = row
    return out


def overhead_table(levels_mw):
    """limit constant with the covering bound |C| <= (m/w)^s (1 + s ln C(m,w)), for slot budget 2^B"""
    z = sum(math.log2(m / w) for m, w in levels_mw)
    out = {}
    for b in (20, 30, 40, 60, 100, 200, 1000, 10000):
        tot = 0.0
        for m, w in levels_mw:
            r = math.log2(m / w)
            if w == 1:
                s = max(1, int(b / r))
            else:
                s = 1
                while (s + 1) * r + math.log2(1 + (s + 1) * math.log(math.comb(m, w))) <= b:
                    s += 1
            tot += b / s
        out[b] = {'Lambda': tot, 'constant': tot / 8}
    return {'ideal_Lambda': z, 'ideal_constant': z / 8, 'by_log2_slots': out}


SA_CPP = r"""// bounded annealing for an exact factorization of the 4-subsets of [N]: lists T_1..T_r of 4-cycles and a family G with
// every 4-subset A having a witness t_r ... t_1 (A) in G. usage: sa N seconds seed m1 .. mr g
#include <bits/stdc++.h>
using namespace std; typedef unsigned u32;
int N; vector<int> rk; vector<u32> subs; mt19937_64 rng;
struct C{int a,b,c,d;};
static inline u32 pre(const C&t,u32 S){u32 sup=(1u<<t.a)|(1u<<t.b)|(1u<<t.c)|(1u<<t.d);u32 A=S&~sup;
 if(S>>t.b&1)A|=1u<<t.a;if(S>>t.c&1)A|=1u<<t.b;if(S>>t.d&1)A|=1u<<t.c;if(S>>t.a&1)A|=1u<<t.d;return A;}
int ri(int n){return rng()%n;}
C rc(){int p[4];for(int i=0;i<4;i++){bool ok;do{ok=true;p[i]=ri(N);for(int j=0;j<i;j++)if(p[j]==p[i])ok=false;}while(!ok);}return {p[0],p[1],p[2],p[3]};}
vector<vector<C>> T; vector<u32> G; vector<int> cov; long unc;
int main(int ac,char**av){N=atoi(av[1]);double tl=atof(av[2]);rng.seed(atol(av[3]));int r=ac-5;T.resize(r);for(int i=0;i<r;i++)T[i].resize(atoi(av[4+i]));int g=atoi(av[ac-1]);G.resize(g);
 rk.assign(1u<<N,-1);for(u32 m=0;m<(1u<<N);m++)if(__builtin_popcount(m)==4){rk[m]=subs.size();subs.push_back(m);}
 int nA=subs.size();cov.assign(nA,0);
 for(auto&l:T)for(auto&t:l)t=rc();for(auto&s:G)s=subs[ri(nA)];
 // contributions by recursion, level r-1 applied last, so preimages go from G through T[r-1]..T[0]
 function<void(int,u32,int)> add=[&](int lv,u32 S,int d){ if(lv<0){int a=rk[S]; if(d>0){if(cov[a]++==0)unc--;}else{if(--cov[a]==0)unc++;}return;} for(auto&t:T[lv])add(lv-1,pre(t,S),d);};
 unc=nA; for(u32 s:G)add(r-1,s,1);
 long best=unc;auto t0=chrono::steady_clock::now();long it=0;double T0=2.0,T1=0.15,temp=T0;
 auto bT=T;auto bG=G;
 while(true){ if((it&0xff)==0){double el=chrono::duration<double>(chrono::steady_clock::now()-t0).count();if(el>tl||best==0)break;temp=T0*pow(T1/T0,el/tl);} it++;
  long before=unc; int tot=g; for(auto&l:T)tot+=l.size(); int q=ri(tot);
  if(q<g){int i=q;u32 old=G[i],nw;if(ri(3)==0)nw=subs[ri(nA)];else{int o;do{o=ri(N);}while(!(old>>o&1));int n;do{n=ri(N);}while(old>>n&1);nw=(old&~(1u<<o))|(1u<<n);}
   add(r-1,old,-1);add(r-1,nw,1);long dl=unc-before; if(dl<=0||(rng()>>11)/(double)(1ull<<53)<exp(-dl/temp))G[i]=nw;else{add(r-1,nw,-1);add(r-1,old,1);}
  } else { q-=g;int lv=0;while(q>=(int)T[lv].size()){q-=T[lv].size();lv++;} C old=T[lv][q],nw=old;int k=ri(5);if(k==4)nw=rc();else{int v=ri(N);int*pp[4]={&nw.a,&nw.b,&nw.c,&nw.d};bool dup=false;for(int j=0;j<4;j++)if(*pp[j]==v)dup=true;if(dup){int a=ri(4),b=ri(4);swap(*pp[a],*pp[b]);}else *pp[k]=v;}
   auto apply=[&](C v,int d){T[lv][q]=v; // contributions through this element only
     function<void(int,u32)> rec=[&](int l2,u32 S){ if(l2==lv){u32 S2=pre(v,S);add(lv-1,S2,d);return;} for(auto&t:T[l2])rec(l2-1,pre(t,S));}; for(u32 s:G)rec(r-1,s);};
   apply(old,-1);apply(nw,1);long dl=unc-before; if(dl<=0||(rng()>>11)/(double)(1ull<<53)<exp(-dl/temp)){}else{apply(nw,-1);apply(old,1);}
  }
  if(unc<best){best=unc;bT=T;bG=G;}
 }
 printf("N=%d sizes",N);for(auto&l:T)printf(" %d",(int)l.size());printf(" g=%d seed=%s best_uncovered=%ld of %d iters=%ld\n",g,av[3],best,nA,it);
 if(best==0){printf("SOL\n");for(auto&l:bT){for(auto&t:l)printf("%d %d %d %d\n",t.a,t.b,t.c,t.d);printf("--\n");}for(u32 s:bG)printf("%u\n",s);}
}
"""


def exact_search(args):
    N, secs, seed = int(args[0]), float(args[1]), int(args[2])
    d = tempfile.mkdtemp()
    src = os.path.join(d, 'sa.cpp')
    open(src, 'w').write(SA_CPP)
    subprocess.check_call(['g++', '-O2', '-std=c++17', '-o', os.path.join(d, 'sa'), src])
    sys.stdout.write(subprocess.check_output([os.path.join(d, 'sa'), str(N), str(secs), str(seed)] + args[3:]).decode())


STATEMENT = """Coordinates of RubiksGN: on an orbit v, k stands for e v k, faceOf (e v k) = kc k (faceOf_e, also on mirror orbits), Word.eval w (e v k) = e v (Rv v w k).
Y = {s : kc o s = kc}. If g acts on v by pi and w by R, then colouring (w.eval * g) (e v k) = kc ((R pi)^-1 k). So the orbit shows faceOf exactly when R pi in Y, i.e. R in Y pi^-1: R has to hit every RIGHT coset of Y, equivalently kc o R = kc o pi^-1.

Certificate. Two lists of template lists, read in time order (x_1 first, R = x_N ... x_1):
  family O, played by rows of the second pass of a round: x_T t = conjT t true * colK^-1 = eT t, x_M t = conjM t true * colM^-1 = eM t (Lean list = reversed time order, R = product of eT in list order);
  family E, played by rows of the first pass: x_T t = colK * conjT t false = (eT t)^-1, x_M t likewise (Lean list = time order, R = (product of eT in list order)^-1).
A place level (orbit o, base b, list l): (P1) every x_T t and x_M t fixes the positions placed so far on its own orbit; (P2) every unplaced position p of orbit o has a t in l with x_o t p = b.
Two final levels A, B on orbit o: (F1) elements act inside the five unplaced positions Omega, the element on the other orbit is 1; (F2) {x_o b * x_o a} = Alt(Omega), 60 distinct; (F3) two points of Omega have the same colour.
Why it suffices. Let s be the current state (partial R times pi); position p holds colour kc(s^-1 p). The unplaced positions holding kc(b) number exactly w = 4 - #{placed positions of colour kc b}, whatever s is, because the placed ones hold their right colours. So exactly w templates of l are good, and they do not depend on the other orbit. The final levels reach any arrangement of Omega (F3 makes the needed permutation even). At the end s in Y, on both orbits.
Exact count: product over the place levels of an orbit of m/w, times 60, equals Z = 24!/24^6. So Lambda := Sum over levels log2(m/w) = 2 log2 Z.

Covering lemma (greedy, no probability): for 1 <= w <= m, s >= 1 there is C subset of (Fin m)^s with |C| <= (m/w)^s * s * ln binom(m,w) + 1 meeting every box W_1 x ... x W_s with |W_i| = w. Proof: a word lies in (w/m)^s of the boxes on average over words, so some word kills that fraction of the remaining boxes.
Use in the program: a job (level, chunk X, |X| = s) takes its patterns from C. For a column j, W_i = good templates of the orbit of (i,j) at that time; patsOf X Y pat subset C, so passW_length_le holds with T = |C| and passW is unchanged. Jobs are decided in order, column by column, since W_i depends on the earlier jobs of the same row and column only.
Rates: s_l = (1 - o(1)) log2 T / log2(m_l/w_l), rounds = Sum_l (S/2)/s_l per half, and the limit constant is Lambda/8 = log2 Z / 4 = 12.88197."""


def main():
    t0 = time.time()
    limit = 8
    srch = Search(limit)
    rng = random.Random(20261104)
    e_t, e_m = 0, 1
    assert len({KCOL[x] for x in KC + (e_t,)}) == 4 and len({KCOL[x] for x in LC + (e_m,)}) == 4
    finals = {}
    for kind, base, e in (('T', KC, e_t), ('M', LC, e_m)):
        r = srch.factorization(base, kind, e)
        assert r, 'no factorization'
        finals[kind] = (r[1], r[2])
        print('final', kind, r[0], round(time.time() - t0), flush=True)
    fams = {}
    for fam in 'OE':
        fams[fam] = build_family(srch, fam, e_t, e_m, finals, rng)
        print('family', fam, [len(l['entries']) for l in fams[fam]], round(time.time() - t0), flush=True)
    mw = [(len(l['entries']), l['w']) for l in fams['O']]
    z = math.factorial(24) // 24 ** 6
    data = {
        'format': 'chain-col2-v1',
        'statement': STATEMENT,
        'K_cycle': list(KC), 'L_common_cycle': list(LC), 'M_cycle': list(canon(cycle_of(COLM))), 'phi': list(PHI),
        'e_target': e_t, 'e_mirror_common': e_m,
        'log2_Z': math.log2(z),
        'families': {fam: {'time_order_levels': fams[fam]} for fam in 'OE'},
        'lean_list_order': {'O': 'reverse of time order, R = product of eT in list order',
                            'E': 'time order, R = (product of eT in list order)^-1'},
        'covering_overhead': overhead_table(mw),
        'finite_n_ratio': finite_table(mw),
        'exact_factorization_search': EXACT_SEARCH,
    }
    with open(OUT, 'w') as f:
        json.dump(data, f, separators=(',', ':'))
    print('written', OUT, os.path.getsize(OUT), round(time.time() - t0))


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--exact-search':
        exact_search(sys.argv[2:])
    else:
        main()
