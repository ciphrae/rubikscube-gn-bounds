"""Adversarial brute-force test of the PLAN.md pass / pair-phase scheme on real cubes.

Full sticker permutations (6n^2 stickers, the integer-vector model of Basic.lean and check_gadget.py).
Word convention as in Lean: a word m1 m2 ... ml evaluates to m1 * m2 * ... * ml, so the head is applied LAST.

Run from the repo root:  uv run python scripts/sim_pass.py [section ...]
Sections: model faithful coverage controls chain endtoend varied cost split   (default: all)
"""
import sys, random, math, itertools, time
from operator import itemgetter
sys.path.insert(0, 'scripts')
from rot import ROT, act, MUL, INV, ID, RX, RY, RZ
from orbit_model import slice_perm, compose, inverse, cycles, IDP, FACES as CF, K as CK_, Rm as CL_, U as GU, Vv as GV

AX = {'x': 0, 'y': 1, 'z': 2}
KC = (5, 13, 21, 19)   # column x=+v on rep(u,v)
LC = (3, 9, 18, 8)     # column x=-v on rep(u,v)
assert cycles(CK_) == [KC] and cycles(CL_) == [LC]
def cyc_perm(c):
    p = list(range(24))
    for i, a in enumerate(c): p[a] = c[(i + 1) % len(c)]
    return tuple(p)
KP, LP = cyc_perm(KC), cyc_perm(LC)
def ppow(p, d): return p if d == 1 else inverse(p)

# ---------------------------------------------------------------- real cube
class Cube:
    def __init__(self, n):
        self.n = n
        C = list(range(-(n - 1), n, 2))
        S = []
        for a in C:
            for b in C:
                for s in (n, -n): S += [(s, a, b), (a, s, b), (a, b, s)]
        self.S = S; self.N = len(S); assert len(set(S)) == 6 * n * n
        self.idx = {v: i for i, v in enumerate(S)}
        self.tab = {}
        self._classify()
        self.inner = [c for c in C if 0 < c < n - 1]
    def clamp(self, t):
        n = self.n
        return n - 1 if t == n else (-(n - 1) if t == -n else t)
    def move_vec(self, m, v):
        ax, layer, d = m
        return ROT[(ax, d)](v) if self.clamp(v[AX[ax]]) == layer else v
    def table(self, m):
        t = self.tab.get(m)
        if t is None:
            src, dst = [], []
            for i, v in enumerate(self.S):
                w = self.move_vec(m, v)
                if w != v: src.append(i); dst.append(self.idx[w])
            t = (itemgetter(*src), dst)
            self.tab[m] = t
        return t
    def eval_word(self, word):
        """permutation P of sticker indices, P = m1*m2*...*ml (ml first)."""
        Q = list(range(self.N))
        for m in reversed(word):
            g, dst = self.table(m)
            vals = g(Q)
            for b, t in zip(dst, vals): Q[b] = t
        P = [0] * self.N
        for pos, s in enumerate(Q): P[s] = pos
        return P
    def eval_naive(self, word, v):
        for m in reversed(word): v = self.move_vec(m, v)
        return v
    def base(self, u, v): return (-u, v, self.n)
    def e(self, u, v, k): return act(k, self.base(u, v))
    def _classify(self):
        """every sticker -> (a,b,k) with sticker = act k (-a,b,n), a>0, b>=0; centres -> ('c',)"""
        n = self.n
        self.cls = {}
        C = [c for c in range(-(n - 1), n, 2)]
        for a in C:
            if a <= 0: continue
            for b in C:
                if b < 0: continue
                for k in range(24):
                    s = act(k, (-a, b, n))
                    assert s not in self.cls, (s, a, b, k)
                    self.cls[s] = (a, b, k)
        for s in self.S:
            if s not in self.cls:
                assert sorted(map(abs, s)) == [0, 0, n], s
                self.cls[s] = ('c',)
    def kind(self, a, b):
        n = self.n
        if a == n - 1 and b == n - 1: return 'corner'
        if a == n - 1 and b == 0: return 'mid-edge'
        if a == n - 1: return 'wing-partner(row0,j)'
        if b == n - 1: return 'wing(i,top)'
        if b == 0: return 'middle-col'
        return 'inner'
    def faces(self):
        n = self.n
        return {'U': ('z', n - 1), 'D': ('z', -(n - 1)), 'F': ('y', n - 1), 'B': ('y', -(n - 1)),
                'r': ('x', n - 1), 'l': ('x', -(n - 1))}

def inv_word(w): return [(a, l, -d) for a, l, d in reversed(w)]

# ---------------------------------------------------------------- pieces f r f^-1 in the 24-coordinate model
FACE_AX = {'U': 'z', 'D': 'z', 'F': 'y', 'B': 'y', 'r': 'x', 'l': 'x'}
EXP = {0: [], 1: [1], 2: [1, 1], 3: [-1]}
class Piece:
    __slots__ = ('perm', 'mask', 'length', 'ax', 'sgn', 'd', 'f')
def build_pieces():
    best = {}
    for ax in 'xyz':
        fs = [f for f in CF if FACE_AX[f] != ax]
        for sgn in (-1, 1):
            for d in (1, -1):
                r = slice_perm(ax, sgn * GU, d)
                for ex in itertools.product(range(4), repeat=4):
                    moves = [(f, t) for f, e in zip(fs, ex) for t in EXP[e]]
                    pf = IDP
                    for f, t in moves: pf = compose(pf, ppow(CF[f], t))
                    perm = compose(compose(pf, r), inverse(pf))
                    p = Piece(); p.perm = perm; p.length = 2 * len(moves) + 1
                    p.ax, p.sgn, p.d, p.f = ax, sgn, d, moves
                    p.mask = sum(1 << i for i in range(24) if perm[i] != i)
                    if perm not in best or best[perm].length > p.length: best[perm] = p
    return list(best.values())
PIECES = build_pieces()
PIECE_OF = {p.perm: p for p in PIECES}
BY_SRC = [sorted(((p.perm[i], p.mask, p) for p in PIECES if p.perm[i] != i), key=lambda t: t[2].length) for i in range(24)]
def path(frm, to, block):
    """pieces (first applied first) moving frm to to, every piece avoiding the blocked points"""
    if frm == to: return []
    prev = {frm: None}; q = [frm]
    for x in q:
        for y, mask, p in BY_SRC[x]:
            if mask & block or y in prev: continue
            prev[y] = (x, p); q.append(y)
            if y == to:
                out = []
                while prev[y] is not None:
                    x_, p_ = prev[y]; out.append(p_); y = x_
                return out[::-1]
    return None
_three = {}
def three_cycles():
    """commutators of pieces sharing one point: 3-cycle perm -> [q^-1, p^-1, q, p], first applied first"""
    if _three: return _three
    rng = random.Random(0); ps = PIECES[:]; rng.shuffle(ps)
    want = 2 * math.comb(24, 3)
    for p in ps:
        pi = inverse(p.perm)
        for q in PIECES:
            m = p.mask & q.mask
            if m == 0 or m & (m - 1): continue
            c = compose(compose(compose(p.perm, q.perm), pi), inverse(q.perm))
            cost = 2 * (p.length + q.length)
            if c not in _three or _three[c][0] > cost:
                _three[c] = (cost, [PIECE_OF[inverse(q.perm)], PIECE_OF[pi], q, p])
        if len(_three) == want: break
    return _three
def macro_step(frm, to, block):
    """BFS over 3-cycle commutators avoiding the blocked points; not every 3-cycle is one commutator"""
    tc = three_cycles()
    prev = {frm: None}; q = [frm]
    for x in q:
        for y in range(24):
            if y in prev or block >> y & 1: continue
            best = None
            for w in range(24):
                if w in (x, y) or block >> w & 1: continue
                p = list(range(24)); p[x] = y; p[y] = w; p[w] = x
                e = tc.get(tuple(p))
                if e is not None and (best is None or e[0] < best[0]): best = e
            if best is None: continue
            prev[y] = (x, best[1]); q.append(y)
            if y == to:
                out = []
                while prev[y] is not None:
                    x_, seq = prev[y]; out = seq + out; y = x_
                return out
    return None
def find_h(pairs, macros=False):
    """pieces p_1..p_l with (p_1*...*p_l)(s)=t for (s,t) in pairs. Returns list in word order, or None.
    Built right to left. With macros=True a blocked point may be passed through a 3-cycle commutator."""
    cur = [s for s, _ in pairs]; applied = []; block = 0
    for j, (_, t) in enumerate(pairs):
        pth = path(cur[j], t, block)
        if pth is None:
            if not macros: return None
            pth = macro_step(cur[j], t, block) if cur[j] != t else []
            if pth is None: return None
        for p in pth:
            cur = [p.perm[c] for c in cur]; applied.append(p)
        block |= 1 << t
    return applied[::-1]
def pieces_perm(ps):
    h = IDP
    for p in ps: h = compose(h, p.perm)
    return h
def pieces_len(ps): return sum(p.length for p in ps)
def template_word(ps, u, cube):
    F = cube.faces(); w = []
    for p in ps:
        f = [F[g] + (t,) for g, t in p.f]
        w += f + [(p.ax, p.sgn * u, p.d)] + inv_word(f)
    return w
def rot4(c, i): return c[i:] + c[:i]
_tcache = {}
def template(c, D, d, offsets=4):
    """shortest found h (over cyclic offsets) with h K^d h^-1 = c and h L^d h^-1 = D"""
    key = (c, D, d)
    t = _tcache.get(key)
    if t is not None: return t
    Ks = KC if d == 1 else (KC[0], KC[3], KC[2], KC[1])
    Ls = LC if d == 1 else (LC[0], LC[3], LC[2], LC[1])
    best = None
    for macros in (False, True):
        for i in range(offsets):
            for j in range(offsets):
                lp = list(zip(Ls, rot4(D, j))); kp = list(zip(Ks, rot4(c, i)))
                for prs in (lp + kp, kp + lp):
                    ps = find_h(prs, macros)
                    if ps is not None and (best is None or pieces_len(ps) < pieces_len(best)): best = ps
        if best is not None: break
    if best is not None:
        h = pieces_perm(best)
        assert compose(compose(h, ppow(KP, d)), inverse(h)) == cyc_perm(c), (c, D, d)
        assert compose(compose(h, ppow(LP, d)), inverse(h)) == cyc_perm(D), (c, D, d)
    _tcache[key] = best
    return best

# ---------------------------------------------------------------- passes
def slot_word(cube, X, pattern, values, cols, d):
    G = []
    for u, vid in zip(X, pattern): G += template_word(values[vid], u, cube)
    return G + [('x', v, d) for v in cols] + inv_word(G)
def pass_word(cube, X, Y, pats, values, d):
    """pats[v] = tuple over X of value ids; values[id] = list of pieces"""
    slots = {}
    for v in Y: slots.setdefault(pats[v], []).append(v)
    w = []
    for p, cols in slots.items(): w += slot_word(cube, X, p, values, cols, d)
    return w, len(slots)
def compare(cube, P, targets):
    """targets {(u,v): perm of Fin 24}. Exact comparison on every sticker; returns first discrepancy or None."""
    for i, s in enumerate(cube.S):
        c = cube.cls[s]
        if c[0] != 'c' and (c[0], c[1]) in targets:
            exp = cube.e(c[0], c[1], targets[(c[0], c[1])][c[2]])
        else:
            exp = s
        got = cube.S[P[i]]
        if got != exp: return dict(sticker=s, cls=c, expected=exp, got=got)
    return None
def random_4cycle(avoid, rng):
    pts = [i for i in range(24) if i not in avoid]
    return tuple(rng.sample(pts, 4))
def canon(c):
    i = c.index(min(c)); return c[i:] + c[:i]

def run_pair_phase(cube, X, Y, rng, m1, m2, nD=1, sabotage=None):
    """random lists, random patterns. nD tags: orbit picks a D then values with that D."""
    Ds = []
    used = set()
    for _ in range(nD):
        D = random_4cycle(used, rng); Ds.append(D); used |= set(D)
    lists1 = {D: [] for D in Ds}; lists2 = {D: [] for D in Ds}
    for D in Ds:
        lists1[D] = [random_4cycle(set(D), rng) for _ in range(m1)]
        lists2[D] = [random_4cycle(set(D), rng) for _ in range(m2)]
    V1, V2, id1, id2 = [], [], {}, {}
    def vid(V, ids, c, D, d):
        k = (c, D)
        if k not in ids:
            t = template(c, D, d); assert t is not None, (c, D, d)
            ids[k] = len(V); V.append(t)
        return ids[k]
    pats1 = {v: [] for v in Y}; pats2 = {v: [] for v in Y}
    targets = {}
    Dinv = lambda D: (D[0], D[3], D[2], D[1])
    for u in X:
        for v in Y:
            D = rng.choice(Ds)
            c1 = rng.choice(lists1[D]); c2 = rng.choice(lists2[D])
            D2 = D
            if sabotage == 'unfrozen': D2 = random_4cycle(set(c2), rng)
            pats1[v].append(vid(V1, id1, c1, D, 1))
            pats2[v].append(vid(V2, id2, c2, Dinv(D2), -1))
            targets[(u, v)] = compose(cyc_perm(c1), cyc_perm(c2))
    pats1 = {v: tuple(p) for v, p in pats1.items()}; pats2 = {v: tuple(p) for v, p in pats2.items()}
    w1, t1 = pass_word(cube, X, Y, pats1, V1, 1)
    w2, t2 = pass_word(cube, X, Y, pats2, V2, -1)
    return w1 + w2, targets, t1, t2, max(pieces_len(t) for t in V1 + V2), (V1, V2)

# ---------------------------------------------------------------- sections
def sec_model():
    print("== model: 24-coordinate actions versus true cubes; phi; groups")
    rng = random.Random(1)
    from sympy.combinatorics import Permutation, PermutationGroup
    # pieces
    print(f" pieces f r f^-1 (distinct 4-cycles): {len(PIECES)}, max length {max(p.length for p in PIECES)}")
    print(f" pieces of which are 4-cycles: {all(len(cycles(p.perm))==1 and len(cycles(p.perm)[0])==4 for p in PIECES)}")
    G = PermutationGroup([Permutation(list(CF[f])) for f in CF] + [Permutation(list(slice_perm(a, s * GU))) for a in 'xyz' for s in (1, -1)])
    print(f" |<faces, six slices>| on one orbit = {G.order()} ; 24! = {math.factorial(24)}; equal: {G.order()==math.factorial(24)}")
    N = PermutationGroup([Permutation(list(p.perm)) for p in PIECES[:]])
    print(f" |balanced group <f r f^-1>| = {N.order()} ; equal 24!: {N.order()==math.factorial(24)}")
    for sub, name in (([p for p in PIECES if p.sgn == 1 and p.ax == 'x'], 'x=+u only'), ([p for p in PIECES if p.ax == 'x'], 'x slices only')):
        g = PermutationGroup([Permutation(list(p.perm)) for p in sub]); print(f"   {name}: order {g.order()} on {len(g.orbits()[0])} pts")
    bad = 0; tested = 0
    for n in (9, 10, 12, 13, 14, 16, 17):
        cube = Cube(n); F = cube.faces()
        # coordinates against the true cube, for every inner orbit pair
        inn = cube.inner
        for u in inn:
            for v in inn:
                if u == v: continue
                def on_cube(m):
                    return tuple(cube.cls[cube.move_vec(m, cube.e(u, v, k))][2] for k in range(24))
                for f, (ax, l) in F.items():
                    tested += 1; bad += on_cube((ax, l, 1)) != CF[f]
                for ax in 'xyz':
                    for s in (1, -1):
                        tested += 1; bad += on_cube((ax, s * u, 1)) != slice_perm(ax, s * GU)
                tested += 2
                bad += on_cube(('x', v, 1)) != KP
                bad += on_cube(('x', -v, 1)) != LP
    print(f" coordinate actions versus true cube: {tested} checks, {bad} mismatches")
    # phi
    sigma = tuple(MUL[k][RZ] for k in range(24))
    trials = fails = 0
    fail_col = 0
    for n in (9, 10, 12, 13, 14, 16, 17):
        cube = Cube(n); inn = cube.inner
        for _ in range(60):
            u, v = rng.sample(inn, 2)
            word = [rng.choice([(a, s * u, rng.choice((1, -1))) for a in 'xyz' for s in (1, -1)] + [(a, l, rng.choice((1, -1))) for a, l in cube.faces().values()]) for _ in range(40)]
            P = cube.eval_word(word)
            pa = tuple(cube.cls[cube.S[P[cube.idx[cube.e(u, v, k)]]]][2] for k in range(24))
            pb = tuple(cube.cls[cube.S[P[cube.idx[cube.e(v, u, k)]]]][2] for k in range(24))
            trials += 1
            fails += compose(compose(sigma, pa), inverse(sigma)) != pb
            # phi on the sticker level: phi flips the sign of the coordinate of abs value v
            for k in range(24):
                s = cube.e(u, v, k); ph = tuple(-c if abs(c) == v else c for c in s)
                img = cube.S[P[cube.idx[s]]]; ph2 = tuple(-c if abs(c) == v else c for c in img)
                if cube.S[P[cube.idx[ph]]] != ph2: fails += 1
            # adding a column of index v must break phi
            P2 = cube.eval_word([('x', v, 1)] + word)
            pa = tuple(cube.cls[cube.S[P2[cube.idx[cube.e(u, v, k)]]]][2] for k in range(24))
            pb = tuple(cube.cls[cube.S[P2[cube.idx[cube.e(v, u, k)]]]][2] for k in range(24))
            fail_col += compose(compose(sigma, pa), inverse(sigma)) != pb
    print(f" phi: {trials} random row words on 7 cubes, {fails} failures (sticker level and pi_b = sigma pi_a sigma^-1, sigma(k)=k*RZ); with one column turn added phi broke {fail_col}/{trials} (expected all)")
    cube = Cube(12); u, v = 3, 7
    gens = []
    def st(m):
        out = []
        for base in ((u, v), (v, u)):
            for k in range(24):
                c = cube.cls[cube.move_vec(m, cube.e(base[0], base[1], k))]
                out.append(c[2] + (0 if (c[0], c[1]) == (u, v) else 24))
        return Permutation(out)
    for a, l in cube.faces().values(): gens.append(st((a, l, 1)))
    for a in 'xyz':
        for s in (1, -1): gens.append(st((a, s * u, 1)))
    g = PermutationGroup(gens)
    print(f" n=12 u=3 v=7, true stickers of rep(u,v) U rep(v,u) under faces+six slices: order {g.order()} = 24! {g.order()==math.factorial(24)}")
    # U-v column added
    g2 = PermutationGroup(gens + [st(('x', v, 1))])
    print(f"   adding column x=+v: order == (24!)^2/2 ?  {g2.order()==math.factorial(24)**2//2}, == (24!)^2 ? {g2.order()==math.factorial(24)**2}")

def sec_faithful():
    print("== faithful: full pair phases, every sticker compared")
    rng = random.Random(2)
    total = 0; stk = 0
    for n, s_, m1, m2, reps in [(9, 2, 4, 4, 4), (10, 2, 4, 4, 4), (12, 2, 6, 5, 4), (13, 2, 6, 5, 4), (14, 3, 6, 5, 4), (16, 3, 6, 5, 4), (17, 3, 6, 5, 4), (25, 4, 5, 5, 2), (32, 5, 4, 4, 2)]:
        cube = Cube(n); t0 = time.time()
        for rep in range(reps):
            nD = 1 + rep % 3
            X = rng.sample(cube.inner, min(s_, len(cube.inner) - 1))
            Yall = [v for v in cube.inner if v not in X]
            Y = rng.sample(Yall, rng.randint(max(1, len(Yall) - 1), len(Yall)))
            w, tg, t1, t2, L, _ = run_pair_phase(cube, X, Y, rng, m1, m2, nD=nD)
            # (d) cost formula with actual slots and actual L
            formula = 2 * len(Y) + (t1 + t2) * 2 * len(X) * L
            assert all(m[2] in (1, -1) for m in w), "qtm"
            assert len(w) <= formula, (len(w), formula)
            P = cube.eval_word(w)
            bad = compare(cube, P, tg)
            moved = sum(1 for i in range(cube.N) if P[i] != i)
            exp_moved = sum(24 - sum(1 for k in range(24) if p[k] == k) for p in tg.values())
            total += 1; stk += cube.N
            print(f" n={n:2d} |X|={len(X)} |Y|={len(Y)} tags={nD} slots={t1}+{t2} L={L} moves={len(w)} formula={formula} moved={moved} predicted_moved={exp_moved} {'OK' if bad is None and moved==exp_moved else 'DISCREPANCY '+str(bad)}")
            if bad: sys.exit("FIRST DISCREPANCY " + str(bad))
        # cross-check the evaluator against the pointwise definition on one short word
        chk = [(rng.choice('xyz'), rng.choice(cube.inner + [n - 1]) * rng.choice((1, -1)), rng.choice((1, -1))) for _ in range(30)]
        P = cube.eval_word(chk)
        assert all(cube.S[P[i]] == cube.eval_naive(chk, s) for i, s in enumerate(cube.S))
    print(f" {total} pair phases, {stk} sticker comparisons, no discrepancy")

def sec_coverage():
    print("== coverage: orbit census; which class each orbit falls into, fixed stickers per class")
    rng = random.Random(3)
    for n in (9, 10, 13, 14, 16, 17):
        cube = Cube(n)
        X = rng.sample(cube.inner, 3 if n > 10 else 2)
        Y = [v for v in cube.inner if v not in X]
        w, tg, t1, t2, L, _ = run_pair_phase(cube, X, Y, rng, 5, 5)
        P = cube.eval_word(w)
        census = {}
        for i, s in enumerate(cube.S):
            c = cube.cls[s]
            if c[0] == 'c': name = 'centre'
            else:
                a, b, _ = c
                name = cube.kind(a, b)
                if name == 'inner':
                    if a in X and b in Y: name = 'target'
                    elif b in X and a in Y: name = 'mirror'
                    elif a == b: name = 'same-index(u,u)' + ('-inX' if a in X else '')
                    elif a in X and b in X: name = 'same-block'
                    else: name = 'plain(u,v notin X)'
                elif name == 'middle-col': name += '-inX' if a in X else ''
                elif name == 'wing(i,top)': name += '-inX' if a in X else ''
                elif name == 'wing-partner(row0,j)': name += '-inX' if b in X else ('-inY' if b in Y else '')
            e = census.setdefault(name, [0, 0])
            e[0] += 1
            e[1] += P[i] != i
        assert sum(v[0] for v in census.values()) == 6 * n * n
        print(f" n={n} X={X} Y={Y}: " + "; ".join(f"{k}:{v[0]}st/{v[1]}moved" for k, v in sorted(census.items())))

def sec_controls():
    print("== negative controls: the comparator must detect broken designs")
    rng = random.Random(4)
    cube = Cube(13)
    X = [2, 6]; Y = [4, 8, 10]
    w, tg, *_ = run_pair_phase(cube, X, Y, rng, 3, 3, sabotage='unfrozen')
    print(" D not frozen across the pair:", compare(cube, cube.eval_word(w), tg))
    w, tg, *_ = run_pair_phase(cube, X, Y + [2], rng, 3, 3)
    print(" column index inside X:", compare(cube, cube.eval_word(w), {k: v for k, v in tg.items() if k[1] != 2}) is not None)
    w, tg, *_ = run_pair_phase(cube, X, Y + [12], rng, 3, 3)
    print(" outer column toggled (x=+(n-1), a face):", compare(cube, cube.eval_word(w), tg) is not None)
    w, tg, *_ = run_pair_phase(cube, X, Y + [0], rng, 3, 3)
    # NOT a failure: on rep(u,0) both copies live on one orbit, the slice acts by K L, and D commutes with c1,c2
    print(" middle column toggled, prediction still c1 c2 (no discrepancy expected, frozen D absorbs it):", compare(cube, cube.eval_word(w), tg))
    # an unbalanced piece: f r without f^-1 in one template
    w, tg, *_ = run_pair_phase(cube, X, Y, rng, 3, 3)
    w2 = list(w); i = next(i for i, m in enumerate(w2) if m[1] == 12 or m[1] == -12)
    del w2[i]
    print(" one face move deleted:", compare(cube, cube.eval_word(w2), tg) is not None)

# ------------------------- exact chain
def small_factor(points):
    """smallest T1,T2 of 4-cycles on `points` with T1*T2 covering the even perms of the points"""
    pts = list(points); idx = range(len(pts))
    fc = []
    for q in itertools.combinations(pts, 4):
        a = q[0]
        for r in itertools.permutations(q[1:]): fc.append((a,) + r)
    def to(c): return cyc_perm(c)
    perms = {c: to(c) for c in fc}
    evens = set()
    for ct in fc:
        for cu in fc: evens.add(compose(perms[ct], perms[cu]))
    return fc, perms, evens

def build_chain(seed=5):
    """b's, D's, T lists; factorisation with stabiliser levels"""
    rng = random.Random(seed)
    pts = list(range(24)); rng.shuffle(pts)
    b = pts[:]
    return b

def ch_value(b, a, omega, forbid=()):
    """4-cycle on omega\\forbid sending b to a (or fixing b if a==b)"""
    free = [p for p in omega if p not in forbid and p not in (b, a)]
    if a == b: return tuple(free[:4])
    return (b, a, free[0], free[1])

class Chain:
    """Pair 1,2 with tags, then frozen D on b1..b4, then endgame on the last four points."""
    def __init__(self, seed=5):
        rng = random.Random(seed)
        self.b = list(range(24)); rng.shuffle(self.b)
        b = self.b
        rest = b[4:]
        # three disjoint tag cycles avoiding b1..b4 for pair 1
        self.D1 = {t: tuple(rest[4 * t:4 * t + 4]) for t in range(3)}
        # for pair 2, D contains b1,b2 and two points
        self.D2 = {t: (b[0], b[1], rest[2 * t], rest[2 * t + 1]) for t in range(3)}
        self.Dstar = tuple(b[:4])
        self.levels = 24
        self.endpts = b[20:]
        fc, perms, evens = small_factor(self.endpts)
        self.end_all = fc; self.end_perm = perms
        # exhaustive search for smallest lists on four points
        best = None
        evenset = {compose(perms[a], perms[c]) for a in fc for c in fc}
        self.A4 = evenset
        for sz1, sz2 in ((3, 4), (4, 3), (4, 4), (5, 3), (3, 5), (5, 4), (4, 5), (5, 5), (6, 3), (3, 6), (6, 4), (4, 6), (6, 5), (5, 6), (6, 6)):
            for T1 in itertools.combinations(fc, sz1):
                for T2 in itertools.combinations(fc, sz2):
                    if {compose(perms[a], perms[c]) for a in T1 for c in T2} >= evenset:
                        best = (T1, T2); break
                if best: break
            if best: break
        self.end1, self.end2 = best
        self.endfac = {compose(perms[a], perms[c]): (a, c) for c in best[1] for a in best[0]}
        self.lists = self._enumerate()
    def tagset(self, a, Dt):
        ok = [t for t in range(3) if a not in Dt[t]]
        return ok[:2]
    def _enumerate(self):
        """all values per list index"""
        b = self.b; L = []
        for k in range(20):
            om = b[k:]
            vals = set()
            for a in om:
                if k < 2:
                    for t in self.tagset(a, self.D1):
                        vals.add((self.value_tagged(k, a, t, self.D1), self.D1[t]))
                elif k < 4:
                    for t in self.tagset(a, self.D2):
                        vals.add((self.value_tagged(k, a, t, self.D2), self.D2[t]))
                else:
                    vals.add((ch_value(b[k], a, om, self.Dstar), self.Dstar))
            L.append(vals)
        L.append({(c, self.Dstar) for c in self.end1})
        L.append({(c, self.Dstar) for c in self.end2})
        return L
    def value_tagged(self, k, a, t, Dt):
        """value independent of the tag whenever that is possible: x,y outside every tag cycle."""
        b = self.b; om = b[k:]
        allD = set().union(*[set(Dt[i]) for i in range(3)])
        free = [p for p in om if p not in allD and p not in (b[k], a)]
        if a == b[k]:
            return tuple(free[:4])
        assert len(free) >= 2
        return (b[k], a, free[0], free[1])
    def factor(self, pi):
        """pi even -> list of (c, D) of length 22 with product c_1*c_2*... = pi"""
        b = self.b; rem = pi; out = []
        for pair in range(10):
            k1, k2 = 2 * pair, 2 * pair + 1
            a1 = rem[b[k1]]
            om1 = b[k1:]
            if pair == 0 or pair == 1:
                Dt = self.D1 if pair == 0 else self.D2
                c1 = self.value_tagged(k1, a1, 0, Dt)   # tag independent
                rem1 = compose(inverse(cyc_perm(c1)), rem)
                a2 = rem1[b[k2]]
                c2 = self.value_tagged(k2, a2, 0, Dt)
                tags = set(self.tagset(a1, Dt)) & set(self.tagset(a2, Dt))
                assert tags, (a1, a2)
                D = Dt[min(tags)]
            else:
                D = self.Dstar
                c1 = ch_value(b[k1], a1, om1, D)
                rem1 = compose(inverse(cyc_perm(c1)), rem)
                a2 = rem1[b[k2]]
                c2 = ch_value(b[k2], a2, b[k2:], D)
            assert not (set(c1) & set(D)) and not (set(c2) & set(D))
            assert all(p not in c1 for p in b[:k1]) and all(p not in c2 for p in b[:k2])
            rem = compose(inverse(cyc_perm(c2)), rem1)
            assert rem[b[k1]] == b[k1] and rem[b[k2]] == b[k2]
            out += [(c1, D), (c2, D)]
        c1, c2 = self.endfac[rem]
        out += [(c1, self.Dstar), (c2, self.Dstar)]
        return out

def random_even(rng):
    p = list(range(24)); rng.shuffle(p); p = tuple(p)
    if sum(len(c) - 1 for c in cycles(p)) % 2: p = compose(p, cyc_perm((0, 1, 2, 3)))
    return p

def sec_chain():
    print("== chain: exact lists, frozen D, tags, endgame")
    rng = random.Random(6)
    ch = Chain()
    sizes = [len(l) for l in ch.lists]
    print(" list sizes", sizes)
    pairs = [(sizes[i], sizes[i + 1]) for i in range(0, len(sizes), 2)]
    Bmax = sum(2 * math.log2(max(p)) for p in pairs)
    Bsum = sum(math.log2(x) for x in sizes)
    print(f" sum over lists log2|T_k| = {Bsum:.3f}; B = sum_pairs 2 log2 max(m1,m2) = {Bmax:.3f}; limit B/4 = {Bmax/4:.3f}; log2(24!/2)={math.log2(math.factorial(24)/2):.3f}, /4 = {math.log2(math.factorial(24)/2)/4:.3f}")
    print(f" endgame lists on the last 4 points: {len(ch.end1)} x {len(ch.end2)}")
    t0 = time.time(); ok = 0
    for _ in range(200000):
        pi = random_even(rng)
        f = ch.factor(pi)
        q = IDP
        for c, _d in f: q = compose(q, cyc_perm(c))
        assert q == pi
        for i, (c, D) in enumerate(f): assert (c, D) in ch.lists[i], (i, c, D)
        ok += 1
    print(f" {ok} random even permutations factored exactly through the lists ({time.time()-t0:.1f}s)")
    # adversarial: images landing in tag cycles
    cnt = 0
    for a1 in range(24):
        for a2 in range(24):
            if a1 == a2: continue
            pi = list(range(24)); b = ch.b
            # build pi with pi(b1)=a1,pi(b2)=a2
            rest = [p for p in range(24) if p not in (a1, a2)]; rng.shuffle(rest)
            pi = [None] * 24; pi[b[0]] = a1; pi[b[1]] = a2
            for j, s in enumerate(b[2:]): pi[s] = rest[j]
            pi = tuple(pi)
            if sum(len(c) - 1 for c in cycles(pi)) % 2:
                x, y = b[2], b[3]; pi = list(pi); pi[x], pi[y] = pi[y], pi[x]; pi = tuple(pi)
            f = ch.factor(pi); q = IDP
            for c, _d in f: q = compose(q, cyc_perm(c))
            assert q == pi; cnt += 1
    print(f" {cnt} permutations with every pair of images of b1,b2 (includes all tag collisions) OK")
    # templates for every value of every list
    tmax = 0; unreachable = []
    t0 = time.time()
    for i, l in enumerate(ch.lists):
        d = 1 if i % 2 == 0 else -1
        for c, D in l:
            DD = D if d == 1 else (D[0], D[3], D[2], D[1])
            t = template(c, DD, d)
            if t is None: unreachable.append((i, c, D))
            else: tmax = max(tmax, pieces_len(t))
    print(f" templates for all {sum(sizes)} values: longest L = {tmax} quarter turns, unreachable: {unreachable} ({time.time()-t0:.1f}s)")
    # (c) exhaustive: every 4-cycle disjoint from D, several D
    Dtests = [ch.Dstar, (0, 3, 10, 19), (0, 1, 4, 11), tuple(rng.sample(range(24), 4)), (8, 16, 21, 11), LC, KC]
    total = 0; fails = []; Lmax = 0; worst = None; nmacro = 0
    t0 = time.time()
    for D in Dtests:
        free = [p for p in range(24) if p not in D]
        for q in itertools.combinations(free, 4):
            for r in itertools.permutations(q[1:]):
                c = (q[0],) + r
                lp = list(zip(LC, D)); kp = list(zip(KC, c))
                ps = find_h(lp + kp) or find_h(kp + lp)
                if ps is None:
                    nmacro += 1
                    ps = find_h(lp + kp, True)
                if ps is None: fails.append((D, c)); continue
                h = pieces_perm(ps)
                if compose(compose(h, KP), inverse(h)) != cyc_perm(c) or compose(compose(h, LP), inverse(h)) != cyc_perm(D):
                    fails.append((D, c, 'wrong')); continue
                l_ = pieces_len(ps)
                if l_ > Lmax: Lmax = l_; worst = (c, D)
                total += 1
    print(f" exhaustive frozen-D: {total} (c,D) pairs over {len(Dtests)} D's all verified by conjugation identity; unreachable {len(fails)} {fails[:5]}; needing commutator macros {nmacro}; longest {Lmax} at {worst} ({time.time()-t0:.1f}s)")
    # verify a random subsample of those through the full conjugation identity
    n_ver = 0
    for _ in range(1500):
        D = rng.choice(Dtests); c = random_4cycle(set(D), rng)
        for d in (1, -1):
            DD = D if d == 1 else (D[0], D[3], D[2], D[1])
            t = template(c, DD, d, offsets=1)   # asserts the identities
            assert t is not None; n_ver += 1
    print(f" {n_ver} random (c,D,d) verified through h K^d h^-1 = c, h L^d h^-1 = D")

def sec_endtoend():
    print("== end-to-end: whole chain on real cubes, random even permutation per orbit")
    rng = random.Random(7)
    ch = Chain()
    for n, s_ in [(9, 2), (10, 2), (12, 2), (13, 2), (14, 3), (16, 3), (17, 3)]:
        cube = Cube(n)
        rows = cube.inner[:]; rng.shuffle(rows)
        blocks = [rows[i:i + s_] for i in range(0, len(rows), s_)]
        block_of = {u: tuple(b) for b in blocks for u in b}
        pi = {}; fac = {}
        for u in rows:
            for v in rows:
                if v not in block_of[u]:
                    pi[(u, v)] = random_even(rng); fac[(u, v)] = ch.factor(pi[(u, v)])
        moves = 0; word = []; form = 0
        for pair in range(11):
            for X in blocks:
                Y = [v for v in rows if v not in X]
                if not Y: continue
                V1, V2, id1, id2 = [], [], {}, {}
                pats1 = {}; pats2 = {}
                for v in Y:
                    p1, p2 = [], []
                    for u in X:
                        (c1, D), (c2, D2) = fac[(u, v)][2 * pair], fac[(u, v)][2 * pair + 1]
                        assert D == D2
                        Dm = (D[0], D[3], D[2], D[1])
                        def vid(V, ids, c, DD, d):
                            if (c, DD) not in ids:
                                t = template(c, DD, d); assert t is not None
                                ids[(c, DD)] = len(V); V.append(t)
                            return ids[(c, DD)]
                        p1.append(vid(V1, id1, c1, D, 1)); p2.append(vid(V2, id2, c2, Dm, -1))
                    pats1[v] = tuple(p1); pats2[v] = tuple(p2)
                w1, t1 = pass_word(cube, X, Y, pats1, V1, 1)
                w2, t2 = pass_word(cube, X, Y, pats2, V2, -1)
                word += w1 + w2
                L = max(pieces_len(t) for t in V1 + V2)
                form += 2 * len(Y) + (t1 + t2) * 2 * len(X) * L
        t0 = time.time()
        P = cube.eval_word(word)
        bad = compare(cube, P, pi)
        print(f" n={n} blocks={[len(b) for b in blocks]} target orbits={len(pi)} moves={len(word)} formula<={form} stickers={cube.N} time={time.time()-t0:.1f}s {'OK' if bad is None else 'DISCREPANCY '+str(bad)}")
        if bad: sys.exit(1)

def sec_cost():
    print("== cost: closed form with the measured L, against the old exact bound")
    ch = Chain()
    sizes = [len(l) for l in ch.lists]
    pairs = [(sizes[i], sizes[i + 1]) for i in range(0, len(sizes), 2)]
    L = 0
    for i, l in enumerate(ch.lists):
        d = 1 if i % 2 == 0 else -1
        for c, D in l:
            t = template(c, D if d == 1 else (D[0], D[3], D[2], D[1]), d); L = max(L, pieces_len(t))
    B = sum(2 * math.log2(max(p)) for p in pairs)
    print(f" pairs {pairs}\n L={L} B={B:.3f} B/4={B/4:.3f}")
    def new(n):
        r = n // 2 - 1; c = n // 2 - 1 if n % 2 == 0 else (n - 3) // 2
        tot = 3 * n + 406
        tot_ex = 0
        main = 0; slots = 0
        for m1, m2 in pairs:
            best = None
            m = max(m1, m2)
            s = 1
            while True:
                T1, T2 = m1 ** s, m2 ** s
                blocks = r // s + 1
                cost = blocks * (2 * c + min(T1, c) * 0 + (min(T1, c) + min(T2, c)) * 2 * s * L) + 275 * 8 * (blocks * s * s)
                if best is None or cost < best[0]: best = (cost, s, blocks)
                if m ** s > 4 * n: break
                s += 1
            tot += best[0]
        tot += 275 * 8 * 2 * r   # outer and middle column
        return tot
    def old(n):
        best = None
        for s in range(1, 4000):
            v = 3 * n + 406 + 275 * ((n // 2 - 1) // s + 1) * ((2 * s + 4) * 2 ** s + 2 * (n - n // 2))
            if best is None or v < best: best = v
            if 2 ** s > 8 * n: break
        return best
    print("   log2 n      new/(n^2/log2 n)   old/(n^2/log2 n)")
    for e in (8, 10, 13, 16, 20, 24, 32, 48, 64, 100, 200, 500, 1000, 4000):
        n = 2 ** e
        print(f"   {e:6d}   {new(n)*e/n**2:14.3f}    {old(n)*e/n**2:14.3f}")

def sec_varied():
    """Each pair phase has its own partition, block sizes differ (leftover chunks), odd n also toggles the middle column.
    Prediction: orbit (u,v) gets the product, in phase order, of c1 c2 over phases in which v is outside u's block."""
    print("== varied: a fresh partition per pair phase, with leftover chunks; middle column toggled for odd n")
    rng = random.Random(8)
    ch = Chain()
    for n in (9, 10, 13, 16, 17, 24, 25, 33):
        cube = Cube(n); rows = cube.inner[:]
        mid = [0] if n % 2 else []
        cols = rows + mid
        fac = {}; pred = {}
        for u in rows:
            for v in cols:
                if v != u: fac[(u, v)] = ch.factor(random_even(rng)); pred[(u, v)] = IDP
        word = []; form = 0
        for pair in range(11):
            s_ = rng.randint(1, 4)
            perm = rows[:]; rng.shuffle(perm)
            blocks = [perm[i:i + s_] for i in range(0, len(perm), s_)]
            for X in blocks:
                Y = [v for v in cols if v not in X]
                if not Y: continue
                V1, V2, id1, id2 = [], [], {}, {}
                pats1 = {}; pats2 = {}
                def vid(V, ids, c, DD, d):
                    if (c, DD) not in ids:
                        t = template(c, DD, d); assert t is not None
                        ids[(c, DD)] = len(V); V.append(t)
                    return ids[(c, DD)]
                for v in Y:
                    p1, p2 = [], []
                    for u in X:
                        (c1, D), (c2, _) = fac[(u, v)][2 * pair], fac[(u, v)][2 * pair + 1]
                        p1.append(vid(V1, id1, c1, D, 1)); p2.append(vid(V2, id2, c2, (D[0], D[3], D[2], D[1]), -1))
                        pred[(u, v)] = compose(pred[(u, v)], compose(cyc_perm(c1), cyc_perm(c2)))
                    pats1[v] = tuple(p1); pats2[v] = tuple(p2)
                w1, t1 = pass_word(cube, X, Y, pats1, V1, 1)
                w2, t2 = pass_word(cube, X, Y, pats2, V2, -1)
                word += w1 + w2
                form += 2 * len(Y) + (t1 + t2) * 2 * len(X) * max(pieces_len(t) for t in V1 + V2)
        t0 = time.time()
        P = cube.eval_word(word)
        assert all(m[2] in (1, -1) for m in word)
        bad = compare(cube, P, pred)
        print(f" n={n} orbits={len(pred)} moves={len(word)} formula<={form} stickers={cube.N} time={time.time()-t0:.1f}s {'OK' if bad is None else 'DISCREPANCY '+str(bad)}")
        if bad: sys.exit(1)

def sec_split():
    """main term, slots, excluded as fractions of the new cost"""
    print("== split of the new cost")
    pairs = [(48, 46), (44, 42), (20, 19), (18, 17), (16, 15), (14, 13), (12, 11), (10, 9), (8, 7), (6, 5), (5, 4)]
    L = 30
    print("  log2n  total*log2n/n^2  main%  slots%  excl%  leftover%  s_values")
    for e in (10, 12, 16, 20, 24, 32, 64, 100, 1000, 4000):
        n = 2 ** e; r = n // 2 - 1; c = r
        M = S_ = Ex = Lo = 0; ss = []
        for m1, m2 in pairs:
            best = None
            m = max(m1, m2); s = 1
            while True:
                bl = r // s + 1; sl = (min(m1 ** s, c) + min(m2 ** s, c)) * 2 * s * L
                ex = 2200 * bl * s * s
                cost = bl * (2 * c + sl) + ex
                if best is None or cost < best[0]: best = (cost, s, bl, sl, ex)
                if m ** s > 4 * n: break
                s += 1
            cost, s, bl, sl, ex = best
            M += (bl - 1) * 2 * c; Lo += 2 * c; S_ += bl * sl; Ex += ex; ss.append(s)
        Ex += 2200 * 2 * r
        T = M + Lo + S_ + Ex + 3 * n + 406
        print(f"  {e:5d}  {T*e/n**2:14.2f}  {100*M/T:5.1f}  {100*S_/T:5.1f}  {100*Ex/T:5.1f}  {100*Lo/T:7.3f}   {ss[0]}..{ss[-1]}")

SECTIONS = dict(model=sec_model, faithful=sec_faithful, coverage=sec_coverage, controls=sec_controls,
                chain=sec_chain, endtoend=sec_endtoend, varied=sec_varied, cost=sec_cost, split=sec_split)
if __name__ == "__main__":
    which = sys.argv[1:] or list(SECTIONS)
    for w in which: SECTIONS[w]()
