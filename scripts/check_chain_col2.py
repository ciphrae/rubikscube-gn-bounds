#!/usr/bin/env python3
"""Independent verifier for scripts/chain_col2.json. Exit status 0 iff every check passes.

Shares no code with chain_col2.py: the only import from the repo is rot.py (rotation model, shared with Lean).
Sections, all from raw definitions (RubiksGN/Basic.lean, PassAction.lean, Pass.lean):
  constants    genP, rowT, rowM, faceA, colK, colM against the `example`s of PassAction.lean; kc; phi
  levels       (P1) (P2) (F1) (F2) (F3) of the JSON statement, for both families; exact product m/w = Z on each orbit
  abstract     random and structured (pi_T, pi_M), choosing at random among the good templates; exact count of good templates
  sidedness    R in Y pi^-1 versus R in pi^-1 Y on a real cube; the wrong family is not regular
  covering     greedy covering lemma, exhaustive on small parameters, with its size bound
  exact        the stored exact factorization for N = 8
  plain        the old lists (scripts/chain_col.json, 13.59) in the scheme with face prefix, abstract run
  real         full programs on real cubes, Lean word order, colouring from its definition

Usage: uv run python scripts/check_chain_col2.py [json path] [--quick] [--large]
"""
import itertools
import json
import math
import os
import random
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rot import act, MUL, INV, RX, RY, RZ, ROT

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print('FAIL:', msg)
    return cond


# ---------------------------------------------------------------- group constants on Fin 24, (a*b)(k) = a[b[k]]
ID = tuple(range(24))
VG = (-1, 2, 3)
AX = {'x': 0, 'y': 1, 'z': 2}
RAX = {'x': RX, 'y': RY, 'z': RZ}


def mul(a, b):
    return tuple(a[x] for x in b)


def inv(a):
    r = [0] * 24
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)


def gen_p(a, c):
    return tuple(MUL[RAX[a]][k] if act(k, VG)[AX[a]] == c else k for k in range(24))


def dpow(d, g):
    return g if d else inv(g)


def face_a(l):
    return dpow(l[2], gen_p(l[0], 3 if l[1] else -3))


def row_t(l):
    return dpow(l[2], gen_p(l[0], 1 if l[1] else -1))


def row_m(l):
    return dpow(l[2], gen_p(l[0], 2 if l[1] else -2))


COLK = gen_p('x', 2)
COLM = gen_p('x', 1)


def lean_examples():
    check(list(COLK) == [0, 1, 2, 3, 4, 13, 6, 7, 8, 9, 10, 11, 12, 21, 14, 15, 16, 17, 18, 5, 20, 19, 22, 23], 'colK example')
    check(list(COLM) == [0, 1, 2, 3, 4, 5, 6, 16, 8, 9, 14, 11, 12, 13, 7, 15, 10, 17, 18, 19, 20, 21, 22, 23], 'colM example')
    check(list(row_t(('y', False, True))) == [0, 1, 2, 6, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19, 3, 21, 22, 23], 'rowT y')
    check(list(row_t(('z', True, True))) == [0, 1, 8, 3, 4, 2, 6, 7, 12, 9, 10, 11, 5, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], 'rowT z')
    check(list(row_m(('y', False, True))) == [0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 15, 11, 10, 13, 14, 4, 16, 17, 18, 19, 20, 21, 22, 23], 'rowM y')
    check(list(row_m(('z', True, True))) == [0, 6, 2, 3, 4, 5, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15, 23, 17, 18, 19, 20, 21, 22, 1], 'rowM z')
    check(list(face_a(('z', True, True))) == [3, 1, 2, 10, 4, 5, 6, 7, 8, 9, 19, 11, 12, 13, 14, 15, 16, 17, 18, 0, 20, 21, 22, 23], 'faceA z')
    check(list(face_a(('z', False, False))) == [0, 1, 2, 3, 18, 5, 6, 13, 8, 9, 10, 11, 12, 4, 14, 15, 16, 17, 7, 19, 20, 21, 22, 23], 'faceA z-')


def fv_face(v, N=3):
    return 0 if v[2] == N else 1 if v[2] == -N else 2 if v[1] == N else 3 if v[1] == -N else 4 if v[0] == N else 5


KC = tuple(fv_face(act(k, (0, 0, 3))) for k in range(24))
FACES = [[k for k in range(24) if KC[k] == c] for c in range(6)]


def is_in_y(s):
    return all(KC[s[k]] == KC[k] for k in range(24))


def eval_tmpl(t, rows):
    h = ID
    for f, r in t:
        fv = ID
        for a, sd, d in f:
            fv = mul(fv, face_a((a, sd, d)))
        h = mul(h, mul(mul(fv, rows(tuple(r))), inv(fv)))
    return h


def conj_t(t, d):
    h = eval_tmpl(t, row_t)
    return mul(mul(h, dpow(d, COLK)), inv(h))


def conj_m(t, d):
    h = eval_tmpl(t, row_m)
    return mul(mul(h, dpow(d, COLM)), inv(h))


def x_elements(fam, t):
    """(x_T, x_M) of a template in a family, from the round formula of PLAN.md: not through eT inverse"""
    if fam == 'O':
        return mul(conj_t(t, True), inv(COLK)), mul(conj_m(t, True), inv(COLM))
    return mul(COLK, conj_t(t, False)), mul(COLM, conj_m(t, False))


def support(p):
    return {k for k in range(24) if p[k] != k}


class Level:
    pass


def load_family(fam, raw):
    levels = []
    for r in raw:
        lv = Level()
        lv.orbit, lv.kind, lv.w = r['orbit'], r['kind'], r['w']
        lv.base = r.get('base')
        lv.tmpl = [e['template'] for e in r['entries']]
        lv.x = [x_elements(fam, t) for t in lv.tmpl]
        levels.append(lv)
    return levels


def check_levels(fam, levels):
    placed = {'T': set(), 'M': set()}
    prod = {'T': Fraction(1), 'M': Fraction(1)}
    finals = {'T': [], 'M': []}
    for n, lv in enumerate(levels):
        o = 0 if lv.orbit == 'T' else 1
        for x in lv.x:
            check(all(x[0][k] == k for k in placed['T']), f'{fam} level {n}: x_T moves a placed position')
            check(all(x[1][k] == k for k in placed['M']), f'{fam} level {n}: x_M moves a placed position')
        if lv.kind == 'place':
            b = lv.base
            check(b not in placed[lv.orbit], f'{fam} level {n}: base already placed')
            free = [p for p in range(24) if p not in placed[lv.orbit]]
            hits = sorted(inv(x[o])[b] for x in lv.x)
            check(hits == free, f'{fam} level {n}: positions sent to the base are exactly the unplaced ones, once each')
            w = 4 - sum(1 for k in placed[lv.orbit] if KC[k] == KC[b])
            check(w == lv.w, f'{fam} level {n}: multiplicity')
            prod[lv.orbit] *= Fraction(len(lv.x), w)
            placed[lv.orbit].add(b)
        else:
            finals[lv.orbit].append(lv)
    z = Fraction(math.factorial(24), 24 ** 6)
    for orb in 'TM':
        o = 0 if orb == 'T' else 1
        check(len(finals[orb]) == 2, f'{fam} {orb}: two final levels')
        omega = [k for k in range(24) if k not in placed[orb]]
        check(len(omega) == 5, f'{fam} {orb}: five points left')
        check(len({KC[k] for k in omega}) == 4, f'{fam} {orb}: two points of one colour, three others (F3)')
        a, b = finals[orb]
        for lv in (a, b):
            for x in lv.x:
                check(support(x[o]) <= set(omega), f'{fam} {orb}: final element inside Omega')
                check(x[1 - o] == ID, f'{fam} {orb}: other element of a final level is 1')
        prods = [mul(xb[o], xa[o]) for xa in a.x for xb in b.x]
        check(len(set(prods)) == 60 and len(prods) == 60, f'{fam} {orb}: final product is 60 distinct elements')
        check(all(sign(p) == 1 for p in prods), f'{fam} {orb}: final products even')
        check(prod[orb] * 60 == z, f'{fam} {orb}: product of m/w times 60 is Z exactly')
    return placed


def sign(p):
    seen = [False] * 24
    s = 1
    for i in range(24):
        if not seen[i]:
            l = 0
            j = i
            while not seen[j]:
                seen[j] = True
                j = p[j]
                l += 1
            if l % 2 == 0:
                s = -s
    return s


# ---------------------------------------------------------------- abstract chain
class Chooser:
    """Picks the template of a level for a state s (the state is the partial product times pi). Colour of position k is kc(s^-1 k)."""

    def __init__(self, levels):
        self.levels = levels
        self.final_pick = {}

    def good(self, n, s, o):
        """indices of the good templates of a place level"""
        lv = self.levels[n]
        si = inv(s)
        return [i for i, x in enumerate(lv.x) if KC[si[inv(x[o])[lv.base]]] == KC[lv.base]]

    def final_pair(self, n, s, o, rng=None):
        """first final level n, second n2: indices (a, b) with x_b x_a s right on Omega"""
        a = self.levels[n]
        b = self.levels[next(m for m in range(n + 1, len(self.levels)) if self.levels[m].orbit == a.orbit and self.levels[m].kind != 'place')]
        out = []
        for ia, xa in enumerate(a.x):
            for ib, xb in enumerate(b.x):
                if is_in_y(mul(mul(xb[o], xa[o]), s)):
                    out.append((ia, ib))
        return out


def run_abstract(levels, pis, rng):
    ch = Chooser(levels)
    s = list(pis)
    pending = {}
    for n, lv in enumerate(levels):
        o = 0 if lv.orbit == 'T' else 1
        if lv.kind == 'place':
            g = ch.good(n, s[o], o)
            check(len(g) == lv.w, f'abstract: level {n} has {len(g)} good templates, expected {lv.w}')
            i = rng.choice(g)
        elif lv.orbit in pending:
            i = pending.pop(lv.orbit)
        else:
            pairs = ch.final_pair(n, s[o], o)
            check(len(pairs) >= 1, f'abstract: no final pair at level {n}')
            i, nxt = rng.choice(pairs)
            pending[lv.orbit] = nxt
        s = [mul(lv.x[i][0], s[0]), mul(lv.x[i][1], s[1])]
    check(is_in_y(s[0]), 'abstract: target not in Y')
    check(is_in_y(s[1]), 'abstract: mirror not in Y')


def section_abstract(fams, trials):
    rng = random.Random(5)
    specials = [ID]
    specials.append(COLK)
    swap = list(range(24))
    swap[FACES[0][0]], swap[FACES[0][1]] = swap[FACES[0][1]], swap[FACES[0][0]]
    specials.append(tuple(swap))        # an odd element of Y
    for fam, levels in fams.items():
        for a, b in itertools.product(specials, specials):
            run_abstract(levels, (a, b), rng)
        for _ in range(trials):
            pa = list(range(24))
            pb = list(range(24))
            rng.shuffle(pa)
            rng.shuffle(pb)
            run_abstract(levels, (tuple(pa), tuple(pb)), rng)


# ---------------------------------------------------------------- non regularity of the other side
def e_family_as_o_counts(fams, trials=2000):
    """The labelled style list (time order E): product P = e_1 ... e_N of eT used directly by O rows, R = P. To have kc o R = f one chooses
    e_1, e_2, ... with e_k(b_k) of colour f(b_k) in the frame left by e_1...e_{k-1}. The number of choices depends on f: this returns the
    spread at each target level, which is what forbids a fixed rate per level on this side."""
    rng = random.Random(7)
    levels = [lv for lv in fams['E'] if lv.orbit == 'T' and lv.kind == 'place']
    # eT t = (x_T t)^-1 in family E
    spread = [set() for _ in levels]
    for _ in range(trials):
        pa = list(range(24))
        rng.shuffle(pa)
        f = [KC[pa[k]] for k in range(24)]
        frame = ID
        for n, lv in enumerate(levels):
            b = lv.base
            good = []
            for i, x in enumerate(lv.x):
                e = inv(x[0])
                if KC[frame[e[b]]] == f[b]:
                    good.append(e)
            spread[n].add(len(good))
            if not good:
                break
            frame = mul(frame, rng.choice(good))
    return [sorted(s) for s in spread]


# ---------------------------------------------------------------- covering lemma
def greedy_cover(m, w, s):
    subs = list(itertools.combinations(range(m), w))
    masks = [sum(1 << x for x in c) for c in subs]
    words = list(itertools.product(range(m), repeat=s))
    boxes = list(itertools.product(range(len(subs)), repeat=s))
    alive = boxes
    code = []
    while alive:
        best, gain = None, -1
        for wd in words:
            g = sum(1 for b in alive if all(masks[b[i]] >> wd[i] & 1 for i in range(s)))
            if g > gain:
                best, gain = wd, g
        code.append(best)
        alive = [b for b in alive if not all(masks[b[i]] >> best[i] & 1 for i in range(s))]
    return code, masks, boxes


def section_covering():
    out = []
    for m, w, s in [(4, 2, 3), (4, 2, 4), (5, 2, 3), (6, 2, 3), (6, 3, 3), (5, 3, 3), (8, 4, 2), (6, 4, 3)]:
        code, masks, boxes = greedy_cover(m, w, s)
        for b in boxes:
            check(any(all(masks[b[i]] >> c[i] & 1 for i in range(s)) for c in code), f'cover ({m},{w},{s}) misses a box')
        bound = (m / w) ** s * (1 + s * math.log(math.comb(m, w))) + 1
        check(len(code) <= bound, f'cover ({m},{w},{s}) above the greedy bound')
        rate = math.log2(len(code)) / s
        out.append((m, w, s, len(code), round(bound, 1), round(rate, 3), round(math.log2(m / w), 3)))
    return out


# ---------------------------------------------------------------- plain old lists, with the face prefix
def section_plain(path, trials=200):
    """Old stage lists, single orbit elements t. With E, E' whole-face 4-cycles (prefix): x = c E^-1, c = E^a t E^-a. With t levels done,
    the state is s_t = E^(N-t) t_t ... t_1 E^-N pi, so the free cycles t act in the frame E^-(N-t). Target levels first, mirror levels second;
    a target level's mirror element is D E'^-1, a mirror level's target element is D E^-1, D a whole-face cycle off c: elements of Y."""
    d = json.load(open(path))
    scheme = d['schemes']['best']

    def perm(c):
        p = list(range(24))
        for i in range(4):
            p[c[i]] = c[(i + 1) % 4]
        return tuple(p)

    def pw(p, a):
        r = ID
        for _ in range(a % 4):
            r = mul(p, r)
        return r
    plains = (perm(FACES[4]), perm(FACES[5]))
    check(is_in_y(plains[0]) and is_in_y(plains[1]), 'face cycles in Y')
    levels = []
    for st in scheme['stages']:
        levels.append(([perm(e['c']) for e in st['list1']], st['colour']))
        levels.append(([perm(e['c']) for e in st['list2']], st['colour']))
    N = len(levels)
    rng = random.Random(3)
    bits = sum(math.log2(len(l)) for l, _ in levels)
    for _ in range(trials):
        pa = list(range(24))
        pb = list(range(24))
        rng.shuffle(pa)
        rng.shuffle(pb)
        s = [tuple(pa), tuple(pb)]
        for phase in (0, 1):
            plain = plains[phase]
            for t, (l, col) in enumerate(levels):
                st = mul(pw(plain, -(N - t)), s[phase])     # state in the frame of the free cycles
                A = [st[k] for k in FACES[col]]
                F = set(FACES[col])
                chosen = None
                if t % 2 == 0:
                    nxt = levels[t + 1][0]
                    for c1 in l:
                        im = [c1[y] for y in A]
                        if any({c2[y] for y in im} == F for c2 in nxt):
                            chosen = c1
                            break
                else:
                    for c2 in l:
                        if {c2[y] for y in A} == F:
                            chosen = c2
                            break
                if not check(chosen is not None, f'plain: no witness stage {col}, level {t}'):
                    return bits
                a = N - 1 - t
                c = mul(mul(pw(plain, a), chosen), pw(plain, -a))
                x = mul(c, inv(plain))
                free = next(f for f in FACES if not set(f) & support(c))
                y = mul(perm(free), inv(plains[1 - phase]))
                check(is_in_y(y), 'plain: the other element is in Y')
                s[phase] = mul(x, s[phase])
                s[1 - phase] = mul(y, s[1 - phase])
        check(is_in_y(s[0]), 'plain: target not in Y')
        check(is_in_y(s[1]), 'plain: mirror not in Y')
    return bits


# ---------------------------------------------------------------- real cube (Basic.lean: sticker vectors, head of a word applied last)
def inverse_list(P):
    r = [0] * len(P)
    for i, x in enumerate(P):
        r[x] = i
    return r


class Cube:
    def __init__(self, n):
        self.n = n
        cs = list(range(-(n - 1), n, 2))
        st = []
        for a in cs:
            for b in cs:
                for s in (n, -n):
                    st += [(s, a, b), (a, s, b), (a, b, s)]
        self.st = st
        self.idx = {v: i for i, v in enumerate(st)}
        self.N = len(st)
        check(len(self.idx) == 6 * n * n, 'sticker count')
        self.tab = {}
        self.face = [self.face_of(v) for v in st]

    def face_of(self, v):
        n = self.n
        return 0 if v[2] == n else 1 if v[2] == -n else 2 if v[1] == n else 3 if v[1] == -n else 4 if v[0] == n else 5

    def clamp(self, t):
        n = self.n
        return n - 1 if t == n else -(n - 1) if t == -n else t

    def table(self, m):
        """pairs (q, q0): the move sends q0 to q"""
        t = self.tab.get(m)
        if t is None:
            ax, layer, d = m
            rot = ROT[(ax, d)]
            t = []
            for i, v in enumerate(self.st):
                if self.clamp(v[AX[ax]]) == layer:
                    t.append((self.idx[rot(v)], i))
            self.tab[m] = t
        return t

    def apply_word(self, word, P):
        """P <- word.eval * P; head of the word is applied last. Works on the inverse, a move touches O(n) entries."""
        Pi = inverse_list(P)
        for m in reversed(word):
            t = self.table(m)
            vals = [Pi[q0] for _, q0 in t]
            for (q, _), x in zip(t, vals):
                Pi[q] = x
        return inverse_list(Pi)

    def identity(self):
        return list(range(self.N))

    def e(self, v, k):
        return self.idx[act(k, v)]

    def orbit_perm(self, P, v):
        """pi with P(e v k) = e v (pi k); fails if P does not preserve the orbit"""
        loc = {self.e(v, k): k for k in range(24)}
        return tuple(loc[int(P[self.e(v, k)])] for k in range(24))


def word_inv(w):
    return [(a, l, -d) for a, l, d in reversed(w)]


def d_of(b):
    return 1 if b else -1


def piece_word(n, u, piece):
    f, r = piece
    fw = [(a, (n - 1) if s else -(n - 1), d_of(d)) for a, s, d in f]
    a, s, d = r
    return fw + [(a, u if s else -u, d_of(d))] + word_inv(fw)


def tmpl_word(n, u, t):
    out = []
    for p in t:
        out += piece_word(n, u, p)
    return out


def g_word(n, pattern):
    out = []
    for u, t in pattern:
        out += tmpl_word(n, u, t)
    return out


def pass_word(n, pats, d):
    """pats: dict column -> tuple of (row, template key); slot per occurring pattern; templates are JSON lists"""
    groups = {}
    for v, pat in pats.items():
        key = json.dumps(pat)
        groups.setdefault(key, (pat, []))[1].append(v)
    out = []
    for key in sorted(groups):
        pat, vs = groups[key]
        g = g_word(n, pat)
        out += g + [('x', v, d_of(d)) for v in vs] + word_inv(g)
    return out, len(groups)


def target_v(n, u, v):
    return (-u, v, n)


def mirror_v(n, u, v):
    return (-v, u, n)


class Program:
    """One coarse block: rows QO, QE, chunk size s for each, columns Y. Patterns from a code."""

    def __init__(self, cube, fams, qo, qe, ys, s, rng, code_factor=None):
        self.cube, self.fams, self.qo, self.qe, self.ys, self.s, self.rng = cube, fams, qo, qe, ys, s, rng
        self.codes = {}
        self.code_factor = code_factor
        self.max_slots = 0

    def code_for(self, fam, n, s):
        """a random code in list^s large enough for the place level n, or None for the whole product"""
        if self.code_factor is None:
            return None
        key = (fam, n, s)
        if key not in self.codes:
            lv = self.fams[fam][n]
            m, w = len(lv.x), lv.w
            if lv.kind != 'place' or w == 1:
                self.codes[key] = None
            else:
                size = min(m ** s, int((m / w) ** s * (1 + self.code_factor * s * math.log(math.comb(m, w)))))
                if size >= m ** s:
                    self.codes[key] = None
                else:
                    r = random.Random(f'{key}')
                    self.codes[key] = {tuple(r.randrange(m) for _ in range(s)) for _ in range(size)}
        return self.codes[key]

    def jobs(self, fam, rows):
        out = []
        levels = self.fams[fam]
        for n in range(len(levels)):
            for i in range(0, len(rows), self.s):
                out.append((n, rows[i:i + self.s]))
        return out

    def run(self, P):
        """returns (word, P after). Patterns are computed from the real position P, one round at a time."""
        c = self.cube
        n = c.n
        jo, je = self.jobs('O', self.qo), self.jobs('E', self.qe)
        word = []
        self.pending = {}
        for t in range(max(len(jo), len(je))):
            pat_o = self.patterns('O', jo[t], P) if t < len(jo) else {v: [] for v in self.ys}
            pat_e = self.patterns('E', je[t], P) if t < len(je) else {v: [] for v in self.ys}
            wo, so = pass_word(n, pat_o, True)
            we, se = pass_word(n, pat_e, False)
            self.max_slots = max(self.max_slots, so, se)
            round_word = wo + we        # roundW = passW XO true ++ passW XE false, head applied last
            P = c.apply_word(round_word, P)
            word = round_word + word
        return word, P

    def patterns(self, fam, job, P):
        n_lv, rows = job
        lv = self.fams[fam][n_lv]
        c = self.cube
        o = 0 if lv.orbit == 'T' else 1
        out = {}
        for v in self.ys:
            goods = []
            for u in rows:
                base = target_v(c.n, u, v) if o == 0 else mirror_v(c.n, u, v)
                st = c.orbit_perm(P, base)      # the colour of position k is kc(st^-1 k)
                if lv.kind == 'place':
                    si = inv(st)
                    # read off the real colouring as well
                    g = [i for i, x in enumerate(lv.x) if KC[si[inv(x[o])[lv.base]]] == KC[lv.base]]
                    check(len(g) == lv.w, f'real: {len(g)} good templates, expected {lv.w}')
                else:
                    key = (fam, lv.orbit, u, v)
                    if key in self.pending:
                        g = [self.pending.pop(key)]
                    else:
                        levels = self.fams[fam]
                        pairs = Chooser(levels).final_pair(n_lv, st, o)
                        check(len(pairs) >= 1, 'real: no final pair')
                        ia, ib = pairs[0]
                        self.pending[key] = ib
                        g = [ia]
                goods.append(g)
            code = self.code_for(fam, n_lv, len(rows))
            if code is None:
                pick = [g[0] for g in goods]
            else:
                pick = next((cw for cw in sorted(code) if all(cw[i] in goods[i] for i in range(len(rows)))), None)
                check(pick is not None, 'real: the code misses a box')
                if pick is None:
                    pick = [g[0] for g in goods]
            out[v] = [(u, lv.tmpl[i]) for u, i in zip(rows, pick)]
        return out


def solved_on(cube, P, stickers):
    """colouring (w * g) q = faceOf (P^-1 q): is it faceOf q on these stickers?"""
    Pi = inverse_list(P)
    return all(cube.face[Pi[q]] == cube.face[q] for q in stickers)


def is_solved_def(cube, P):
    """IsSolved (colouring ...): the literal definition, faces monochromatic"""
    Pi = inverse_list(P)
    seen = {}
    for q in range(cube.N):
        if seen.setdefault(cube.face[q], cube.face[Pi[q]]) != cube.face[Pi[q]]:
            return False
    return True


def random_word(cube, rng, length):
    n = cube.n
    layers = list(range(-(n - 1), n, 2))
    return [(rng.choice('xyz'), rng.choice(layers), rng.choice((1, -1))) for _ in range(length)]


def orbit_stickers(cube, base):
    return [cube.e(base, k) for k in range(24)]


def section_real(fams, configs, seeds):
    """Program on a real cube with a full random scramble: handled orbits come out right, the word is the identity elsewhere."""
    res = []
    for n, qo, qe, ys, s, cf in configs:
        cube = Cube(n)
        for seed in seeds:
            rng = random.Random(seed)
            g = random_word(cube, rng, 30 * n * n)
            P0 = cube.apply_word(g, cube.identity())
            prog = Program(cube, fams, qo, qe, ys, s, rng, cf)
            word, P = prog.run(P0)
            handled = []
            for u in qo + qe:
                for v in ys:
                    handled.append(target_v(n, u, v))
                    handled.append(mirror_v(n, u, v))
            hs = {x for b in handled for x in orbit_stickers(cube, b)}
            ok = solved_on(cube, P, sorted(hs))
            check(ok, f'real n={n} seed={seed}: handled orbits not solved')
            W = cube.apply_word(word, cube.identity())
            others = [q for q in range(cube.N) if q not in hs]
            check(all(W[q] == q for q in others), f'real n={n} seed={seed}: word moves an orbit it should fix')
            check(prog.max_slots <= len(ys), f'real n={n}: slots')
            # the literal colouring is not solved here (other orbits are scrambled); parity of the handled orbits:
            odd = sum(1 for b in handled if sign(cube.orbit_perm(P0, b)) == -1)
            res.append((n, tuple(qo), tuple(qe), tuple(ys), s, seed, len(word), prog.max_slots, odd))
    return res


def section_real_full(fams, n, blocks, seeds):
    """All cross block pairs: the scramble acts only on those orbits, built from random rounds. The literal IsSolved must hold after the programs."""
    res = []
    cube = Cube(n)
    for seed in seeds:
        rng = random.Random(seed)
        P = cube.identity()
        progs = []
        for bi, blk in enumerate(blocks):
            ys = [v for b2 in blocks[bi + 1:] for v in b2]
            if not ys:
                continue
            h = len(blk) // 2
            progs.append((blk[:h], blk[h:], ys))
        scramble = []
        for qo, qe, ys in progs:
            for _ in range(12):
                po = {v: [(u, rng.choice(rng.choice(fams['O']).tmpl)) for u in qo] for v in ys}
                pe = {v: [(u, rng.choice(rng.choice(fams['E']).tmpl)) for u in qe] for v in ys}
                w = pass_word(n, po, True)[0] + pass_word(n, pe, False)[0]
                scramble = w + scramble
        P = cube.apply_word(scramble, P)
        check(not is_solved_def(cube, P), f'real full n={n}: the scramble is trivial')
        total = 0
        for qo, qe, ys in progs:
            prog = Program(cube, fams, qo, qe, ys, 1, rng, None)
            word, P = prog.run(P)
            total += len(word)
        check(is_solved_def(cube, P), f'real full n={n} seed={seed}: IsSolved fails')
        res.append((n, seed, len(scramble), total))
    return res


def face_template():
    """BFS on images of K under pieces: a template h with h K h^-1 a 4-cycle on one face"""
    pieces = []
    letters = [(a, s, d) for a in 'xyz' for s in (True, False) for d in (True, False)]
    for r in letters:
        pieces.append(([], r))
        for f in letters:
            pieces.append(([list(f)], r))
    start = (5, 13, 21, 19)
    seen = {start: []}
    fr = [start]
    while fr:
        nx = []
        for st in fr:
            for pc in pieces:
                p = eval_tmpl([pc], row_t)
                t = tuple(p[x] for x in st)
                if t not in seen:
                    seen[t] = [pc] + seen[st]
                    if len({KC[x] for x in t}) == 1:
                        return seen[t], t
                    nx.append(t)
        fr = nx
    return None


def section_sidedness(seeds):
    """g arbitrary, pi on an orbit. m is a slot with R_m = E, a face cycle, so E in Y on that orbit. R = E pi^-1 solves the orbit, R = pi^-1 E does not."""
    tm, cyc = face_template()
    n = 10
    cube = Cube(n)
    u, v = 3, 5
    base = target_v(n, u, v)
    orb = orbit_stickers(cube, base)
    out = []
    for seed in seeds:
        rng = random.Random(seed)
        g = random_word(cube, rng, 2000)
        P0 = cube.apply_word(g, cube.identity())
        pi = cube.orbit_perm(P0, base)
        gi = word_inv(g)
        m, _ = pass_word(n, {v: [(u, tm)]}, True)
        Rm = cube.orbit_perm(cube.apply_word(m, cube.identity()), base)
        check(is_in_y(Rm) and Rm != ID, 'sidedness: slot acts by a nontrivial element of Y')
        check(Rm == conj_t(tm, True), 'sidedness: slot action is conjT')
        good = cube.apply_word(m + gi, P0)   # m after g^-1: R = E pi^-1, R pi = E
        bad = cube.apply_word(gi + m, P0)    # g^-1 after m: R = pi^-1 E, R pi = pi^-1 E pi
        Rg = cube.orbit_perm(good, base)
        Rb = cube.orbit_perm(bad, base)
        check(solved_on(cube, good, orb) == is_in_y(Rg), 'sidedness: orbit solved iff R pi in Y (good)')
        check(solved_on(cube, bad, orb) == is_in_y(Rb), 'sidedness: orbit solved iff R pi in Y (bad)')
        check(solved_on(cube, good, orb), 'sidedness: right coset solves')
        # colouring formula pointwise on one sticker per k
        Pi = inverse_list(bad)
        Rbi = inv(Rb)
        check(all(cube.face[Pi[cube.e(base, k)]] == KC[Rbi[k]] for k in range(24)), 'sidedness: colour of position k is kc(R pi)^-1 k')
        out.append(solved_on(cube, bad, orb))
    return out, cyc


def section_exact_n8(data):
    """the stored exact factorization of the 4-subsets of 8 points"""
    f = data['exact_factorization_search']['found']
    target = set(f['target_set'])

    def image(c, a):
        m = {c[i]: c[(i + 1) % 4] for i in range(4)}
        return {m.get(x, x) for x in a}
    t1, t2 = f['first_applied'], f['second_applied']
    check(len(t1) * len(t2) == 70, 'exact N=8: sizes')
    for a in itertools.combinations(range(f['N']), 4):
        hits = sum(1 for c1 in t1 for c2 in t2 if image(c2, image(c1, a)) == target)
        check(hits == 1, f'exact N=8: {a} has {hits} witnesses')


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    quick = '--quick' in sys.argv
    here = os.path.dirname(os.path.abspath(__file__))
    path = args[0] if args else os.path.join(here, 'chain_col2.json')
    data = json.load(open(path))
    lean_examples()
    check(all(len(f) == 4 for f in FACES), 'faces')
    phi = tuple(data['phi'])
    check(all(KC[phi[k]] == KC[k] for k in range(24)), 'phi preserves colours')
    # phi carries L (x = -2 on the target model) to colM, rows to rows
    check(mul(mul(inv(phi), COLM), phi) == gen_p('x', -2), 'phi^-1 colM phi = L')
    for l in [(a, s, d) for a in 'xyz' for s in (True, False) for d in (True, False)]:
        check(mul(mul(inv(phi), row_m(l)), phi) == row_t(l), 'rows diagonal in common coordinates')
    fams = {fam: load_family(fam, data['families'][fam]['time_order_levels']) for fam in 'OE'}
    for fam in fams:
        check_levels(fam, fams[fam])
    mw = {o: [(len(lv.x), lv.w) for lv in fams['O'] if lv.kind == 'place' and lv.orbit == o] for o in 'TM'}
    lam = sum(math.log2(m / w) for o in 'TM' for m, w in mw[o]) + 2 * math.log2(60)
    z = math.log2(math.factorial(24) / 24 ** 6)
    check(abs(lam - 2 * z) < 1e-9, 'Lambda = 2 log2 Z')
    section_abstract(fams, 50 if quick else 600)
    spread = e_family_as_o_counts(fams, 300 if quick else 2000)
    check(any(len(s) > 1 for s in spread), 'expected irregular counts on the other side')
    section_exact_n8(data)
    cov = section_covering()
    plain = section_plain(os.path.join(here, 'chain_col.json'), 20 if quick else 150)
    side, cyc = section_sidedness(range(3 if quick else 10))
    real_cfg = [(10, [1], [3], [5, 7], 1, None), (11, [2], [4], [6, 8], 1, None), (12, [1], [3], [5, 7, 9], 1, None),
                (14, [1, 3], [5, 7], [9, 11], 2, 2.0), (16, [1, 3], [5, 7], [9, 11, 13], 2, 2.0)]
    if quick:
        real_cfg = real_cfg[:1]
    if '--large' in sys.argv:
        real_cfg = [(64, [1, 3, 5, 7], [9, 11, 13, 15], list(range(17, 63, 2)), 4, 2.0)]
    real = section_real(fams, real_cfg, range(1 if '--large' in sys.argv else 2 if quick else 3))
    full = section_real_full(fams, 10, [[1, 3], [5, 7]], range(1 if quick else 3))
    if not quick:
        full += section_real_full(fams, 12, [[1, 3], [5, 7], [9]], range(2))
        full += section_real_full(fams, 13, [[2, 4], [6, 8], [10]], range(2))
    if FAILS:
        print(len(FAILS), 'failures')
        sys.exit(1)
    print('levels O:', [(len(l.x), l.w) for l in fams['O']])
    print('levels E:', [(len(l.x), l.w) for l in fams['E']])
    print(f'Lambda = {lam:.6f}, Lambda/8 = {lam / 8:.6f}, log2 Z / 4 = {z / 4:.6f}')
    print('wrong side, counts of good templates at the target levels (min..max):', [(min(s), max(s)) for s in spread if s])
    print('covering (m,w,s,|C|,bound,rate,log2(m/w)):', cov)
    if plain is not None:
        print(f'plain lists with face prefix: Sigma log2 m = {plain:.4f} per orbit, Lambda/8 = {plain / 4:.4f}')
    print('sidedness: wrong coset solved in', sum(side), 'of', len(side), 'runs; right coset always; face cycle', cyc)
    print('real (n,QO,QE,Y,s,seed,moves,slots,odd handled orbits):')
    for r in real:
        print('  ', r)
    print('real full IsSolved (n,seed,scramble moves,program moves):', full)
    print('OK')


if __name__ == '__main__':
    main()
