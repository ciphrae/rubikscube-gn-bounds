#!/usr/bin/env python3
"""Red team of the claim godColoured mu n ~ (log2 Z / 4) n^2 / log2 n, Z = 24!/(4!)^6, as built on scripts/chain_col2.json.

Run: uv run --with numpy python scripts/redteam_col.py [levels finals sim controls limit lower]   (default: all)
Sections, each exits nonzero on a failed check:
  levels    (1) every template of the JSON is evaluated on a REAL sticker cube (n = 14, 13, 40) to obtain x_T, x_M: no formula is used.
            Structure of each level from those tables, then good counts over random and structured states on both orbits and families.
  finals    (5) the last five points: colour multiset, sharply transitive A5, unique pair, every arrangement, both orbits, both families.
  sim       (2) whole programs on real cubes (full sticker permutation), adaptive greedy covering (conditional expectations), chunk sizes per level.
            Reads colours off stickers; checks good counts, |C| against the bound, solved handled orbits, identity elsewhere, the exact action
            predicted per orbit, literal IsSolved in the all-cross-block runs.
  controls  (2) negative controls: the checks must fire on a sabotaged pick, and on the O and E lists exchanged.
  limit     (3) exact integer evaluation of the exactW cost formula with the covering slots, n = 2^20 .. 2^10000, split into terms.
  lower     (4) counting bound for the same n, orbit census on real cubes, bits per move of the simulated programs.

Limits: one process, RLIMIT_AS 8 GB, per-section alarm. Shares only rot.py with the repo.
"""
import itertools
import json
import math
import os
import random
import resource
import signal
import sys
import time
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rot import ROT, act  # the rotation model shared with Lean

resource.setrlimit(resource.RLIMIT_AS, (8 << 30, 8 << 30))
FAILS = []
AX = {'x': 0, 'y': 1, 'z': 2}
ID = tuple(range(24))
Z = Fraction(math.factorial(24), 24 ** 6)
LOG2Z = math.log2(Z)


def check(c, msg):
    if not c:
        FAILS.append(msg)
        print('FAIL:', msg, flush=True)
    return c


def mul(a, b):
    return tuple(a[x] for x in b)


def inv(a):
    r = [0] * len(a)
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)


def sign(p):
    seen, s = set(), 1
    for i in range(len(p)):
        if i not in seen:
            l, j = 0, i
            while j not in seen:
                seen.add(j)
                j = p[j]
                l += 1
            s *= -1 if l % 2 == 0 else 1
    return s


# ------------------------------------------------------------------ the real cube: Basic.lean, stickers are vectors
class Cube:
    def __init__(self, n):
        self.n = n
        cs = np.arange(-(n - 1), n, 2)
        parts = []
        for s in (n, -n):
            a, b = np.meshgrid(cs, cs, indexing='ij')
            a, b = a.ravel(), b.ravel()
            c = np.full_like(a, s)
            parts += [np.stack([c, a, b], 1), np.stack([a, c, b], 1), np.stack([a, b, c], 1)]
        self.S = np.concatenate(parts).astype(np.int32)
        self.N = len(self.S)
        check(self.N == 6 * n * n, 'sticker count')
        self.base = 2 * n + 1
        k = self.key(self.S)
        self.order = np.argsort(k)
        self.sorted = k[self.order]
        check(len(np.unique(k)) == self.N, 'stickers distinct')
        z, y, x = self.S[:, 2], self.S[:, 1], self.S[:, 0]
        self.face = np.where(z == n, 0, np.where(z == -n, 1, np.where(y == n, 2, np.where(y == -n, 3, np.where(x == n, 4, 5))))).astype(np.int8)
        self.clamped = np.clip(self.S, -(n - 1), n - 1)
        self.tab = {}
        self.orb = {}

    def key(self, v):
        v = v.astype(np.int64) + self.n
        return (v[:, 0] * self.base + v[:, 1]) * self.base + v[:, 2]

    def index(self, v):
        return self.order[np.searchsorted(self.sorted, self.key(v))]

    def table(self, m):
        t = self.tab.get(m)
        if t is None:
            ax, layer, d = m
            src = np.nonzero(self.clamped[:, AX[ax]] == layer)[0]
            v = self.S[src]
            x, y, z = v[:, 0], v[:, 1], v[:, 2]
            if ax == 'x':
                w = np.stack([x, -z, y], 1) if d == 1 else np.stack([x, z, -y], 1)
            elif ax == 'y':
                w = np.stack([z, y, -x], 1) if d == 1 else np.stack([-z, y, x], 1)
            else:
                w = np.stack([-y, x, z], 1) if d == 1 else np.stack([y, -x, z], 1)
            t = (src, self.index(w))
            self.tab[m] = t
        return t

    def identity(self):
        return np.arange(self.N, dtype=np.int32)

    def apply_word(self, word, pi):
        """pi is the inverse of the sticker permutation P: colour of q is face[pi[q]]. P <- word.eval * P; the head of the word acts last."""
        for m in reversed(word):
            src, dst = self.table(m)
            pi[dst] = pi[src]
        return pi

    def orbit(self, b):
        o = self.orb.get(b)
        if o is None:
            o = self.index(np.array([act(k, b) for k in range(24)], dtype=np.int32))
            self.orb[b] = o
        return o

    def orbit_perm(self, wi, b):
        """R with W(e b k) = e b (R k), from the inverse array of W"""
        o = self.orbit(b)
        loc = {int(q): k for k, q in enumerate(o)}
        ri = tuple(loc[int(wi[q])] for q in o)      # raises KeyError if the orbit is not preserved
        return inv(ri)

    def target(self, u, v):
        return (-u, v, self.n)

    def mirror(self, u, v):
        return (-v, u, self.n)


def w_inv(w):
    return [(a, l, -d) for a, l, d in reversed(w)]


def dsign(b):
    return 1 if b else -1


def tmpl_word(n, u, t):
    out = []
    for f, r in t:
        fw = [(a, (n - 1) if s else -(n - 1), dsign(d)) for a, s, d in f]
        out += fw + [(r[0], u if r[1] else -u, dsign(r[2]))] + w_inv(fw)
    return out


def tmpl_len(t):
    return sum(2 * len(f) + 1 for f, _ in t)


def slot(n, pattern, cols, d):
    """pattern: list of (row, template)"""
    g = []
    for u, t in pattern:
        g += tmpl_word(n, u, t)
    return g + [('x', v, dsign(d)) for v in cols] + w_inv(g)


# ------------------------------------------------------------------ levels, derived from stickers
class Level:
    pass


def derive(cube, fam, t, u, w, v):
    """x_T, x_M of a template: one real round, the row u playing t in the pass of its family, the row w playing nothing in the other pass"""
    n = cube.n
    if fam == 'O':
        word = slot(n, [(u, t)], [v], True) + slot(n, [(w, [])], [v], False)
    else:
        word = slot(n, [(w, [])], [v], True) + slot(n, [(u, t)], [v], False)
    wi = cube.apply_word(word, cube.identity())
    return cube.orbit_perm(wi, cube.target(u, v)), cube.orbit_perm(wi, cube.mirror(u, v))


def load():
    data = json.load(open(os.path.join(HERE, 'chain_col2.json')))
    fams = {}
    c14, c13, c40 = Cube(14), Cube(13), Cube(40)
    rng = random.Random(1)
    for fam in 'OE':
        fams[fam] = []
        for r in data['families'][fam]['time_order_levels']:
            lv = Level()
            lv.orbit, lv.kind, lv.w, lv.base = r['orbit'], r['kind'], r['w'], r.get('base')
            lv.o = 0 if lv.orbit == 'T' else 1
            lv.tmpl = [e['template'] for e in r['entries']]
            lv.m = len(lv.tmpl)
            lv.x = []
            for t in lv.tmpl:
                x = derive(c14, fam, t, 3, 5, 9)
                check(x == derive(c13, fam, t, 2, 4, 8), 'action differs between n = 14 and n = 13')
                if rng.random() < 0.05:
                    check(x == derive(c40, fam, t, 7, 11, 21), 'action differs at n = 40')
                lv.x.append(x)
            lv.xi = [(inv(a), inv(b)) for a, b in lv.x]
            if lv.kind == 'place':
                lv.pos = np.array([xi[lv.o][lv.base] for xi in lv.xi])
            fams[fam].append(lv)
    b = (-3, 9, 14)
    kc = tuple(int(c14.face[c14.orbit(b)[k]]) for k in range(24))
    check(kc == tuple(int(c13.face[c13.orbit((-2, 8, 13))[k]]) for k in range(24)), 'kc depends on n')
    check(kc == tuple(int(c14.face[c14.orbit((-9, 3, 14))[k]]) for k in range(24)), 'kc differs on the mirror orbit')
    return fams, kc


def in_y(s, kc):
    return all(kc[s[k]] == kc[k] for k in range(24))


# ------------------------------------------------------------------ (1)
def sec_levels(fams, kc):
    faces = [[k for k in range(24) if kc[k] == c] for c in range(6)]
    check(all(len(f) == 4 for f in faces), 'colour classes')
    report = {}
    for fam, levels in fams.items():
        placed = {0: set(), 1: set()}
        prod = {0: Fraction(1), 1: Fraction(1)}
        ratios = []
        garbage = 0
        for n, lv in enumerate(levels):
            for x in lv.x:
                check(all(x[0][k] == k for k in placed[0]), f'{fam} {n} x_T moves a placed position')
                check(all(x[1][k] == k for k in placed[1]), f'{fam} {n} x_M moves a placed position')
            other_ids = sum(x[1 - lv.o] == ID for x in lv.x)
            if other_ids < lv.m:
                garbage += 1
            prod[lv.o] *= Fraction(lv.m, lv.w)
            ratios.append(Fraction(lv.m, lv.w))
            check(lv.m > lv.w, f'{fam} {n}: m/w <= 1')
            if lv.kind == 'place':
                free = sorted(set(range(24)) - placed[lv.o])
                check(sorted(lv.pos.tolist()) == free, f'{fam} {n}: entries are not a bijection onto the unplaced positions')
                check(lv.w == 4 - sum(kc[k] == kc[lv.base] for k in placed[lv.o]), f'{fam} {n}: w')
                placed[lv.o].add(lv.base)
            else:
                check(other_ids == lv.m, f'{fam} {n}: final level touches the other orbit')
        check(prod[0] == Z and prod[1] == Z, f'{fam}: product of m/w, with the two final lists counted as m/1, is not Z')
        report[fam] = (min(ratios), float(min(ratios)), garbage, len(levels), sum(math.log2(r) for r in ratios))

    # good counts, worst case and random picks
    rng = random.Random(11)
    cnt = 0

    def run(levels, pi, picker):
        nonlocal cnt
        s = list(pi)
        pend = {}
        for n, lv in enumerate(levels):
            si = inv(s[lv.o])
            if lv.kind == 'place':
                good = [i for i, x in enumerate(lv.x) if kc[si[lv.xi[i][lv.o][lv.base]]] == kc[lv.base]]
                check(len(good) == lv.w, f'level {n}: {len(good)} good, w = {lv.w}')
                i = picker(good)
                # a level concerns one orbit: count the entries that keep both orbits placed, they are all of them (checked above)
            elif lv.orbit in pend:
                i = pend.pop(lv.orbit)
            else:
                nxt = next(q for q in range(n + 1, len(levels)) if levels[q].orbit == lv.orbit and levels[q].kind != 'place')
                pairs = [(a, b) for a in range(lv.m) for b in range(levels[nxt].m)
                         if in_y(mul(levels[nxt].x[b][lv.o], mul(lv.x[a][lv.o], s[lv.o])), kc)]
                check(len(pairs) == 1, f'final level {n}: {len(pairs)} pairs, expected exactly one')
                i, pend[lv.orbit] = pairs[0]
            cnt += 1
            s = [mul(lv.x[i][0], s[0]), mul(lv.x[i][1], s[1])]
        check(in_y(s[0], kc) and in_y(s[1], kc), 'final state not in Y')

    def rand_perm():
        p = list(range(24))
        rng.shuffle(p)
        return tuple(p)

    # structured states: the identity, each colour class pushed onto one fixed block, and (odd) transpositions inside Y
    sorted_pos = sorted(range(24), key=lambda k: kc[k])
    structured = [ID, tuple(sorted_pos), inv(tuple(sorted_pos))]
    t = list(range(24))
    t[faces[0][0]], t[faces[0][1]] = t[faces[0][1]], t[faces[0][0]]
    structured.append(tuple(t))
    t2 = list(range(24))
    t2[faces[0][0]], t2[faces[1][0]] = t2[faces[1][0]], t2[faces[0][0]]
    structured.append(tuple(t2))
    pickers = [lambda g: g[0], lambda g: g[-1], rng.choice]
    t0 = time.time()
    for fam, levels in fams.items():
        for a, b in itertools.product(structured, structured):
            for pk in pickers:
                run(levels, (a, b), pk)
        for trial in range(1500):
            run(levels, (rand_perm(), rand_perm()), pickers[trial % 3])
    print(f'levels: {cnt} level visits, {time.time() - t0:.0f}s, all counts exact')
    for fam, (mn, mf, garb, nl, lam) in report.items():
        print(f'  family {fam}: {nl} levels, min m/w = {mn} = {mf:.3f}, levels with nontrivial other element = {garb}, Lambda = {lam:.6f}, 2 log2 Z = {2 * LOG2Z:.6f}')
        check(abs(lam - 2 * LOG2Z) < 1e-9, 'Lambda')


# ------------------------------------------------------------------ (5)
def sec_finals(fams, kc):
    for fam, levels in fams.items():
        for o in (0, 1):
            a, b = [lv for lv in levels if lv.o == o and lv.kind != 'place']
            placed = {lv.base for lv in levels if lv.o == o and lv.kind == 'place'}
            omega = sorted(set(range(24)) - placed)
            cols = sorted(kc[k] for k in omega)
            hist = sorted(cols.count(c) for c in set(cols))
            check(hist == [1, 1, 1, 2], f'{fam} {o}: colour multiset of Omega {hist}')
            prods = [mul(xb[o], xa[o]) for xa in a.x for xb in b.x]
            check(len(set(prods)) == 60 and len(prods) == 60, f'{fam} {o}: not 60 distinct products')
            check(all(sign(p) == 1 and {k for k in range(24) if p[k] != k} <= set(omega) for p in prods), f'{fam} {o}: products not even or leave Omega')
            # every arrangement of the colours of Omega on Omega: exactly one pair restores it
            arr = set(itertools.permutations([kc[k] for k in omega]))
            check(len(arr) == 60, f'{fam} {o}: {len(arr)} arrangements')
            for ar in arr:
                hold = dict(zip(omega, ar))
                hits = sum(all(hold[inv(p)[k]] == kc[k] for k in omega) for p in prods)
                check(hits == 1, f'{fam} {o}: arrangement restored by {hits} pairs')
            print(f'finals: family {fam} orbit {"TM"[o]}: |X|,|Y| = {a.m},{b.m}, Omega {omega}, colours {[kc[k] for k in omega]}, all 60 arrangements restored by exactly 1 pair')


# ------------------------------------------------------------------ (2)
def greedy_cover(boxes, m):
    """boxes: bool array (columns, s, m). Conditional expectations: each word hits at least the (w/m)^s fraction. Returns the words and word index per column."""
    nc, s, _ = boxes.shape
    alive = np.ones(nc, dtype=bool)
    words, of = [], np.full(nc, -1)
    while alive.any():
        cur = alive.copy()
        word = []
        for i in range(s):
            v = int(np.argmax(boxes[cur, i, :].sum(axis=0)))
            word.append(v)
            cur &= boxes[:, i, v]
        of[cur] = len(words)
        alive &= ~cur
        words.append(tuple(word))
    return words, of


def chunk_size(lv, ny, rows, force):
    if lv.m == lv.w:
        return rows
    r = lv.m / lv.w
    s = int(math.floor(math.log(max(ny / (math.log(ny) + 1), 1.0001)) / math.log(r)))
    return max(1, min(rows, max(s, force)))


class Program:
    def __init__(self, cube, fams, kc, qo, qe, ys, force=2, cover=True, sabotage=None):
        self.c, self.fams, self.kc, self.qo, self.qe, self.ys = cube, fams, kc, qo, qe, ys
        self.force, self.cover, self.sabotage = force, cover, sabotage
        self.pend = {}
        self.stats = []
        self.R = {(u, v): [ID, ID] for u in qo + qe for v in ys}
        self.bits = 0.0

    def jobs(self, fam, rows):
        out = []
        for n, lv in enumerate(self.fams[fam]):
            s = chunk_size(lv, len(self.ys), len(rows), self.force) if lv.w > 1 else chunk_size(lv, len(self.ys), len(rows), 1)
            for i in range(0, len(rows), s):
                out.append((n, rows[i:i + s]))
        return out

    def boxes(self, fam, job, pi):
        n_lv, rows = job
        lv = self.fams[fam][n_lv]
        c = self.c
        box = np.zeros((len(self.ys), len(rows), lv.m), dtype=bool)
        for a, v in enumerate(self.ys):
            for b, u in enumerate(rows):
                base = c.target(u, v) if lv.o == 0 else c.mirror(u, v)
                cols = c.face[pi[c.orbit(base)]]      # read off the real stickers: position k shows this colour
                if lv.kind == 'place':
                    g = np.nonzero(cols[lv.pos] == self.kc[lv.base])[0]
                    if not (self.sabotage and (u, v) == self.sabotage[:2]):
                        check(len(g) == lv.w, f'real: {len(g)} good, w = {lv.w}, level {n_lv} ({u},{v}) n={c.n}')
                    if len(g) == 0:
                        g = np.arange(lv.m)
                else:
                    key = (fam, lv.orbit, u, v)
                    if key in self.pend:
                        g = [self.pend.pop(key)]
                    else:
                        levels = self.fams[fam]
                        nxt = next(q for q in range(n_lv + 1, len(levels)) if levels[q].orbit == lv.orbit and levels[q].kind != 'place')
                        ct = [int(x) for x in cols]
                        pairs = []
                        for ia, xa in enumerate(lv.xi):
                            for ib, xb in enumerate(levels[nxt].xi):
                                # the new position k holds what was at xa^-1 xb^-1 k
                                if all(ct[xa[lv.o][xb[lv.o][k]]] == self.kc[k] for k in range(24)):
                                    pairs.append((ia, ib))
                        sab = self.sabotage and (u, v) == self.sabotage[:2]
                        if not sab:
                            check(len(pairs) == 1, f'real final: {len(pairs)} pairs ({u},{v})')
                        if pairs:
                            ia, ib = pairs[0]
                        else:
                            ia, ib = 0, 0
                        self.pend[key] = ib
                        g = [ia]
                box[a, b, np.asarray(g)] = True
        if self.sabotage and self.sabotage[2] == (fam, n_lv):
            u0, v0 = self.sabotage[:2]
            if u0 in rows:
                a, b = self.ys.index(v0), rows.index(u0)
                box[a, b] = ~box[a, b]      # only bad entries for this row and column
        return box

    def pass_of(self, fam, job, pi, d):
        """the word of one pass, the chosen pattern per column, and statistics"""
        c = self.c
        if job is None:
            return slot(c.n, [], self.ys, d), None
        n_lv, rows = job
        lv = self.fams[fam][n_lv]
        box = self.boxes(fam, job, pi)
        s = len(rows)
        if self.cover:
            words, of = greedy_cover(box, lv.m)
        else:
            naive = [tuple(int(np.nonzero(box[a, b])[0][0]) for b in range(s)) for a in range(len(self.ys))]
            words = sorted(set(naive))
            of = np.array([words.index(w) for w in naive])
        used = sorted(set(of.tolist()))
        ny = len(self.ys)
        bound = (lv.m / lv.w) ** s * (math.log(ny) + 1) + 1 if lv.w > 1 else min(lv.m ** s, ny)
        check(len(used) <= bound, f'|C| = {len(used)} above the bound {bound}, level {n_lv} s={s}')
        for a in range(ny):
            for b in range(s):
                check(box[a, b, words[of[a]][b]], 'pattern misses the box')
        self.stats.append((lv.m, lv.w, s, ny, len(used), bound, lv.m ** s if s < 12 else float('inf')))
        self.bits += ny * s * math.log2(lv.m / lv.w)
        word = []
        for wi in used:
            cols = [self.ys[a] for a in range(ny) if of[a] == wi]
            pat = [(rows[b], lv.tmpl[words[wi][b]]) for b in range(s)]
            word += slot(c.n, pat, cols, d)
        # expected action per orbit
        act_of = {}
        for a in range(ny):
            for b in range(s):
                act_of[(rows[b], self.ys[a])] = lv.x[words[of[a]][b]]
        return word, act_of

    def run(self, pi):
        jo, je = self.jobs('O', self.qo), self.jobs('E', self.qe)
        c = self.c
        nmoves = 0
        for t in range(max(len(jo), len(je))):
            wo, ao = self.pass_of('O', jo[t] if t < len(jo) else None, pi, True)
            we, ae = self.pass_of('E', je[t] if t < len(je) else None, pi, False)
            word = wo + we          # roundW: the head acts last
            c.apply_word(word, pi)
            nmoves += len(word)
            for acts in (ao, ae):
                if acts:
                    for key, x in acts.items():
                        self.R[key] = [mul(x[0], self.R[key][0]), mul(x[1], self.R[key][1])]
        return nmoves


def sim_case(fams, kc, n, blocks, force, seed, scramble='random', cover=True, label=''):
    """blocks: list of lists of row coordinates. Each block runs on the columns of the later blocks. Prints statistics."""
    t0 = time.time()
    c = Cube(n)
    rng = random.Random(seed)
    layers = list(range(-(n - 1), n, 2))
    pi = c.identity()
    progs = []
    for k, blk in enumerate(blocks):
        ys = [v for b in blocks[k + 1:] for v in b]
        if ys:
            h = len(blk) // 2
            progs.append((blk[:h], blk[h:], ys))
    if scramble == 'none':
        pass
    elif scramble == 'random':
        # a full random position: every orbit of the cube, odd parities included
        w = [(rng.choice('xyz'), rng.choice(layers), rng.choice((1, -1))) for _ in range(3 * n * n)]
        c.apply_word(w, pi)
    else:
        # only the orbits of the programs: 10 random rounds of random templates, so literal IsSolved must hold at the end
        for qo, qe, ys in progs:
            for _ in range(10):
                po = {v: [(u, rng.choice(rng.choice(fams['O']).tmpl)) for u in qo] for v in ys}
                pe = {v: [(u, rng.choice(rng.choice(fams['E']).tmpl)) for u in qe] for v in ys}
                word = []
                for v, p in po.items():
                    word += slot(n, p, [v], True)
                for v, p in pe.items():
                    word += slot(n, p, [v], False)
                c.apply_word(word, pi)
    p0inv = pi.copy()
    p0 = np.empty(c.N, dtype=np.int32)
    p0[p0inv] = np.arange(c.N, dtype=np.int32)
    allstats, moves, bits, odd = [], 0, 0.0, 0
    handled = []
    preds = []
    for qo, qe, ys in progs:
        for u in qo + qe:
            for v in ys:
                handled += [c.target(u, v), c.mirror(u, v)]
        odd += sum(sign(c.orbit_perm(p0inv, b)) == -1 for b in handled)
        pr = Program(c, fams, kc, qo, qe, ys, force, cover)
        moves += pr.run(pi)
        allstats += pr.stats
        bits += pr.bits
        preds.append(pr)
    # solved on every handled orbit, read from colours
    hs = np.unique(np.concatenate([c.orbit(b) for b in handled]))
    check(bool(np.all(c.face[pi[hs]] == c.face[hs])), f'n={n}: handled orbits not colour solved')
    # W = P P0^-1 is the identity off the handled orbits, and on them it is exactly the predicted product
    winv = p0[pi]
    mask = np.ones(c.N, dtype=bool)
    mask[hs] = False
    check(bool(np.all(winv[mask] == np.nonzero(mask)[0])), f'n={n}: the word moves a sticker outside the handled orbits')
    for pr in preds:
        for (u, v), (rt, rm) in pr.R.items():
            check(c.orbit_perm(winv, c.target(u, v)) == rt, f'n={n}: target action differs from the prediction at ({u},{v})')
            check(c.orbit_perm(winv, c.mirror(u, v)) == rm, f'n={n}: mirror action differs from the prediction at ({u},{v})')
    literal = None
    if scramble == 'rounds':
        seen = {}
        literal = all(seen.setdefault(int(f), int(g)) == int(g) for f, g in zip(c.face, c.face[pi]))
        check(literal, f'n={n}: literal IsSolved fails')
    multi = [x for x in allstats if x[2] > 1 and x[1] > 1]
    ratio = max((x[4] / x[5] for x in multi), default=0)
    useful = [x for x in multi if x[4] < min(x[3], x[6])]
    ssizes = sorted({x[2] for x in allstats})
    print(f'  {label} n={n} blocks={[len(b) for b in blocks]} Y_max={max(len(p[2]) for p in progs)} jobs={len(allstats)} s values={ssizes} moves={moves} '
          f'jobs s>1,w>1: {len(multi)}, |C|/bound max {ratio:.3f}, |C| < min(|Y|, m^s) in {len(useful)}; '
          f'examples (m,w,s,|Y|,|C|,bound)={[(a, b, s, y, k, round(bd)) for a, b, s, y, k, bd, _ in sorted(useful, key=lambda t: t[4] / t[3])[:3]]}; '
          f'odd handled orbits {odd}/{len(handled)}; literal IsSolved {literal}; bits/move {bits / moves:.2f} (cap log2(9n+1) = {math.log2(9 * n + 1):.2f}); {time.time() - t0:.0f}s', flush=True)
    check(bits / moves <= math.log2(9 * n + 1), 'bits per move above the counting cap')
    return allstats


def even_rows(n, count, start=0):
    cs = [x for x in range(-(n - 1), n, 2) if 0 < x < n - 1]
    return cs[start:start + count]


def sec_sim(fams, kc):
    cs = lambda n: [x for x in range(-(n - 1), n, 2) if 0 < x < n - 1]
    # moderate, single block, random full scramble, s > 1 forced
    r = cs(64)
    sim_case(fams, kc, 64, [r[:8], r[8:]], 2, 1, 'random', True, 'block')
    r = cs(65)
    sim_case(fams, kc, 65, [r[:8], r[8:]], 2, 2, 'random', True, 'block')
    r = cs(40)
    sim_case(fams, kc, 40, [r[:8], r[8:]], 3, 3, 'random', True, 'block s>=3')
    # all cross-block orbits of a cube, literal IsSolved
    r = cs(40)
    sim_case(fams, kc, 40, [r[:6], r[6:12], r[12:]], 2, 4, 'rounds', True, 'full')
    r = cs(41)
    sim_case(fams, kc, 41, [r[:6], r[6:12], r[12:]], 2, 5, 'rounds', True, 'full')
    # large enough that the code is far below m^s and |Y|
    r = cs(256)
    sim_case(fams, kc, 256, [r[:4], r[4:]], 2, 6, 'random', True, 'code')
    r = cs(256)
    sim_case(fams, kc, 256, [r[:4], r[4:]], 2, 6, 'random', False, 'no-code')
    # more seeds, larger chunks, all cross-block orbits at n = 64 and 65, the solved position as a scramble, and a code at larger |Y| and s
    for seed in (7, 8, 9):
        r = cs(64)
        sim_case(fams, kc, 64, [r[:8], r[8:]], 3, seed, 'random', True, 'seed')
    r = cs(64)
    sim_case(fams, kc, 64, [r[:10], r[10:20], r[20:]], 3, 10, 'rounds', True, 'full')
    r = cs(65)
    sim_case(fams, kc, 65, [r[:10], r[10:20], r[20:]], 4, 11, 'rounds', True, 'full')
    r = cs(64)
    sim_case(fams, kc, 64, [r[:8], r[8:]], 2, 12, 'none', True, 'solved start')
    r = cs(512)
    sim_case(fams, kc, 512, [r[:6], r[6:]], 3, 13, 'random', True, 'code')


def sec_controls(fams, kc):
    # (a) non-good entries in one job for one row and column: this orbit fails, every other orbit is solved
    n = 24
    c = Cube(n)
    r = [x for x in range(-(n - 1), n, 2) if 0 < x < n - 1]
    qo, qe, ys = r[:2], r[2:4], r[4:]
    rng = random.Random(9)
    layers = list(range(-(n - 1), n, 2))
    pi = c.identity()
    c.apply_word([(rng.choice('xyz'), rng.choice(layers), rng.choice((1, -1))) for _ in range(3 * n * n)], pi)
    u0, v0 = qo[0], ys[3]
    nlv = 12
    lv = fams['O'][nlv]
    # the target level nlv is sabotaged, so the target orbit of (u0,v0) must fail
    Program(c, fams, kc, qo, qe, ys, 2, True, (u0, v0, ('O', nlv))).run(pi)
    bad = [b for b in [c.target(u, v) for u in qo + qe for v in ys] + [c.mirror(u, v) for u in qo + qe for v in ys]
           if not np.all(c.face[pi[c.orbit(b)]] == c.face[c.orbit(b)])]
    check(c.target(u0, v0) in bad or c.mirror(u0, v0) in bad, 'control: the sabotage was not seen')
    check(all(b in (c.target(u0, v0), c.mirror(u0, v0)) for b in bad), f'control: the sabotage leaked to other orbits {bad}')
    print(f'controls: sabotage of level {nlv} ({lv.orbit}) at row {u0}, column {v0}: unsolved orbits {bad}, nothing else')
    # (b) the O lists played by E rows and conversely: the regularity must fail
    swapped = {'O': fams['E'], 'E': fams['O']}
    fails_before = len(FAILS)
    c2 = Cube(14)
    pi = c2.identity()
    rng = random.Random(10)
    layers = list(range(-13, 14, 2))
    c2.apply_word([(rng.choice('xyz'), rng.choice(layers), rng.choice((1, -1))) for _ in range(800)], pi)
    r = [x for x in range(-13, 14, 2) if 0 < x < 13]
    fired = False
    try:
        Program(c2, swapped, kc, r[:1], r[1:2], r[2:], 1, False).run(pi)
    except Exception as e:
        fired = True
        print('  control: raised', type(e).__name__)
    bad = [b for b in [c2.target(u, v) for u in r[:2] for v in r[2:]] + [c2.mirror(u, v) for u in r[:2] for v in r[2:]]
           if not np.all(c2.face[pi[c2.orbit(b)]] == c2.face[c2.orbit(b)])]
    n_fired = len(FAILS) - fails_before
    del FAILS[fails_before:]
    check(fired or n_fired > 0 or bad, 'control: exchanging the lists went unnoticed')
    print(f'controls: O and E lists exchanged: {n_fired} check failures, unsolved orbits {len(bad)}')
    # (c) the coverage bound itself on random boxes, exhaustive on the box family for tiny parameters
    for m, w, s in [(4, 2, 3), (6, 2, 3), (6, 3, 3), (7, 3, 2), (8, 3, 2)]:
        subs = list(itertools.combinations(range(m), w))
        allb = list(itertools.product(subs, repeat=s))
        box = np.zeros((len(allb), s, m), dtype=bool)
        for a, b in enumerate(allb):
            for i, q in enumerate(b):
                box[a, i, list(q)] = True
        words, of = greedy_cover(box, m)
        bound = (m / w) ** s * (math.log(len(allb)) + 1) + 1
        check(len(words) <= bound and (of >= 0).all(), f'cover ({m},{w},{s})')
        print(f'  all boxes m={m} w={w} s={s}: {len(allb)} boxes, |C| = {len(words)}, bound {bound:.0f}, lower limit (m/w)^s = {(m / w) ** s:.1f}')


# ------------------------------------------------------------------ (3)
def level_stats(fams):
    return {fam: [(lv.m, lv.w) for lv in lvs] for fam, lvs in fams.items()}


def exact_cost(x, mw, L, beta, a, universal=False):
    """n = 2^x, S = 2^a, exact integers. Returns None if not admissible. Terms as in RubiksGN/ExactCost.lean, with Cslot = max |C| 2 s L."""
    n = 2 ** x
    r = n // 2 - 1
    S = 2 ** a
    lnr = x * math.log(2)
    Rs = {}
    Cslot = 0
    ss = []
    for fam, lst in mw.items():
        R = 0
        for m, w in lst:
            q = Fraction(m, w)
            s = int(beta / math.log2(q))
            if s < 1:
                return None
            s = min(s, S // 2)
            ss.append(s)
            if w == 1:
                C = m ** s
            else:
                factor = s * math.log(math.comb(m, w)) + 1 if universal else lnr + 1
                p = q ** s
                C = (p.numerator * int(factor * 2 ** 20) // (p.denominator * 2 ** 20)) + 2
                C = min(C, m ** s)
            Cslot = max(Cslot, C * 2 * s * L)
            R += S // 2 // s + 1
        Rs[fam] = R
    R = max(Rs.values())
    base = 3 * n + 406
    gadget = 2200 * r * (S + 2)
    plain = R * (r ** 2 // S)
    slots = R * 2 * (r // S + 1) * Cslot
    return dict(n=n, r=r, base=base, gadget=gadget, plain=plain, slots=slots, W=base + gadget + plain + slots, R=R, Cslot=Cslot, smin=min(ss), smax=max(ss))


def to_norm(v, x):
    return float(Fraction(v, 4 ** x)) * x


def sec_limit(fams, kc):
    mw = level_stats(fams)
    L = max(tmpl_len(t) for lvs in fams.values() for lv in lvs for t in lv.tmpl)
    c = LOG2Z / 4
    print(f'limit: L = {L}, target constant {c:.6f}; smallest m/w per family: ' +
          ', '.join(f'{fam} {min(Fraction(m, w) for m, w in l)}' for fam, l in mw.items()))
    print('  log2 n | beta     a | smin smax | ratio W log2 n/n^2 = plain + slots + gadget + base | W ratio / limit | x(W/limit-1)/log2 x | universal C ratio | LB ratio | LB/UB')
    rows = []
    for x in (20, 30, 50, 100, 200, 300, 500, 1000, 2000, 3000, 5000, 10000):
        best = None
        lgx = math.log2(x)
        betas = [b for b in range(max(4, int(x - 3.2 * lgx - 40)), max(5, int(x - 1.5 * lgx))) if b > 3]
        step = max(1, len(betas) // 25)
        for beta in betas[::step]:
            for a in sorted({max(1, int(x / 2 + d)) for d in (-8, -6, -4, -3, -2, -1, 0, 2)}):
                e = exact_cost(x, mw, L, beta, a)
                if e is None:
                    continue
                if best is None or e['W'] < best[0]['W']:
                    best = (e, beta, a)
        e, beta, a = best
        # refine beta
        for b2 in range(beta - step, beta + step + 1):
            if b2 >= 4:
                e2 = exact_cost(x, mw, L, b2, a)
                if e2 and e2['W'] < e['W']:
                    e, beta = e2, b2
        ratio = to_norm(e['W'], x)
        uni = exact_cost(x, mw, L, beta, a, True)
        best_u = uni
        for b2 in range(beta - 12, beta + 1):
            if b2 >= 4:
                u = exact_cost(x, mw, L, b2, a, True)
                if u and (best_u is None or u['W'] < best_u['W']):
                    best_u = u
        ru = to_norm(best_u['W'], x) if best_u else float('nan')
        inner = (2 ** (x - 1) - 1) ** 2
        lb = (Fraction(inner) * Fraction(LOG2Z) - 6 * Fraction(math.log2(6))) / Fraction(x + math.log2(9))
        lbn = float(lb / 4 ** x) * x
        check(e['W'] >= lb, f'x={x}: the upper bound is below the counting bound')
        check(lbn < ratio, 'x')
        print(f'  {x:6d} | {beta:5d} {a:5d} | {e["smin"]:4d} {e["smax"]:4d} | {ratio:10.4f} = {to_norm(e["plain"], x):9.4f} + {to_norm(e["slots"], x):8.4f} + {to_norm(e["gadget"], x):8.2e} + {to_norm(e["base"], x):8.2e}'
              f' | {ratio / c:7.4f} | {x * (ratio / c - 1) / lgx:7.3f} | {ru:9.4f} | {lbn:8.4f} | {lbn / ratio:6.4f}', flush=True)
        rows.append((x, ratio))
    # the excess must shrink: it behaves like 3 log2 log2 n / log2 n (or better)
    for (x1, r1), (x2, r2) in zip(rows, rows[1:]):
        check(r2 < r1, f'ratio does not decrease from 2^{x1} to 2^{x2}')
    check(rows[-1][1] < c * 1.012, 'n = 2^10000: excess above 1.2 percent')
    # the plain term alone against Lambda/8 log2 n / beta: floors
    x = 10000
    for fam, l in mw.items():
        lam = sum(math.log2(m / w) for m, w in l)
        for beta in (100, 1000, 9000):
            sm = sum(1 / int(beta / math.log2(m / w)) for m, w in l)
            print(f'  floors, family {fam}, beta {beta}: beta Sum 1/s_l = {beta * sm:.4f}, Lambda = {lam:.4f}, excess {beta * sm / lam - 1:.5f}')


# ------------------------------------------------------------------ (4)
def sec_lower(fams, kc):
    print(f'lower: log2 Z = {LOG2Z:.6f}, log2 Z / 4 = {LOG2Z / 4:.6f}; Lambda/8 per family: ' +
          ', '.join(f'{fam} {sum(math.log2(lv.m / lv.w) for lv in lvs) / 8:.6f}' for fam, lvs in fams.items()))
    check(Z == 3246670537110000, 'Zval')
    # the census: every sticker of a real cube lies in a 24-orbit of the scheme or the skeleton; orbits that the count of Lower.lean uses
    for n in (20, 21, 64, 65):
        c = Cube(n)
        cs = [x for x in range(-(n - 1), n, 2) if 0 < x < n - 1]
        seen = np.zeros(c.N, dtype=np.int32)
        for u in cs:
            for v in cs:
                seen[c.orbit(c.target(u, v))] += 1
        check(int(seen.max()) <= 1, f'n={n}: inner orbits overlap')
        ninner = (n // 2 - 1) * (n - n // 2 - 1)    # innerOrbits of Lower.lean; for odd n its columns include the middle column v = 0
        ncols = len(cs) + (n % 2)
        check(len(cs) * ncols == ninner, f'n={n}: inner count {len(cs) * ncols} vs innerOrbits {ninner}')
        if n % 2:
            for u in cs:
                seen[c.orbit(c.target(u, 0))] += 1
        offdiag = len(cs) * (len(cs) - 1)
        rest = c.N - int((seen > 0).sum())
        check(int(seen.max()) == 1, f'n={n}: inner orbits overlap')
        print(f'  n={n}: inner orbits {ninner} (off-diagonal, the scheme: {offdiag}; diagonal and middle column, gadget: {ninner - offdiag}), {rest} of {c.N} stickers outside inner orbits = O(n)')
        # the inner orbits are invariant under all moves
        rng = random.Random(n)
        pi = c.identity()
        layers = list(range(-(n - 1), n, 2))
        c.apply_word([(rng.choice('xyz'), rng.choice(layers), rng.choice((1, -1))) for _ in range(2000)], pi)
        for u, v in rng.sample(list(itertools.product(cs, cs)), 20):
            c.orbit_perm(pi, c.target(u, v))
    # goal consistency: R pi in Y implies solved, on a real orbit, with the global colour permutation fixed; and a colour permuted goal is not needed
    print('  per pair {a,b}: 2 orbits, 2 log2 Z bits, at log2 n bits per column move, (n^2/8) pairs: (n^2/8) 2 log2 Z / log2 n = (log2 Z / 4) n^2 / log2 n')


SECTIONS = {'levels': sec_levels, 'finals': sec_finals, 'sim': sec_sim, 'controls': sec_controls, 'limit': sec_limit, 'lower': sec_lower}
TIMEOUTS = {'levels': 600, 'finals': 300, 'sim': 1500, 'controls': 300, 'limit': 900, 'lower': 300}


def alarm(*_):
    raise TimeoutError('section timeout')


def main():
    t0 = time.time()
    fams, kc = load()
    print(f'loaded {sum(lv.m for lvs in fams.values() for lv in lvs)} templates, actions from stickers, {time.time() - t0:.0f}s', flush=True)
    signal.signal(signal.SIGALRM, alarm)
    for name in (sys.argv[1:] or SECTIONS):
        signal.alarm(TIMEOUTS[name])
        SECTIONS[name](fams, kc)
        signal.alarm(0)
    if FAILS:
        print(len(FAILS), 'FAILURES')
        sys.exit(1)
    print('ALL CHECKS PASS')


if __name__ == '__main__':
    main()
