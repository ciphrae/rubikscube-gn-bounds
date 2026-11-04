"""Generate scripts/exact_chain.json: the 42 universal template lists of the exact round scheme (PLAN.md).

Conventions are those of RubiksGN/PassAction.lean, with permutations of Fin 24 as tuples and (a*b)(k) = a[b[k]].
  h  = evalT t,  h' = evalTm t
  eT t = h colK h^-1 colK^-1,  eM t = h' colM h'^-1 colM^-1.

Common coordinates: phi flips the coordinate of absolute value 2 and carries the target model (-1,2,3) to the
mirror model, so that h' = phi h phi^-1 for every template. Hence (c, D0) = (h K h^-1, h L h^-1), with
L = phi^-1 colM phi the layer x = -2, and the raw mirror cycle is D = phi(D0). The search below takes place in common
coordinates, and every output is written in raw coordinates.

Design. Om = supp K + {e}, Om' = supp L + {e'}, Z = the other 14 points. In common coordinates
  T1,M1,...,T5,M5: the target places Om', the mirror places Om, with c avoiding the target points placed so far and D0 the
                   mirror points placed so far, and the other element arbitrary;
  T-late:          the target places Z, with D0 = L (mirror element 1), sizes 19..6;
  M-late:          the mirror places Z, with c = K (target element 1), sizes 19..6;
  T-final:         lists X, Y on Om, |X| = 5, |Y| = 12, X*Y = Alt(Om), mirror element 1;
  M-final:         the same on Om'.
A base point b is never in the support of the commutator partner, so e(b) = c(b), and the entry with image b is the
empty template (c = K, D0 = L: both elements are 1).

L = 8 is the optimum for this design: the last list pair of a chain has its other element equal to 1, and with
that restriction no exact 5 x 12 or 12 x 5 factorization has both lists below cost 8 (`--test-seven` checks this).

Pure Python, about one minute on one core. Usage: uv run python scripts/exact_chain.py
"""
import functools
import itertools
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rot import MUL, RX, RY, RZ, act

LIMIT = 8
ID = tuple(range(24))
VG = (-1, 2, 3)
AX = {'x': (0, RX), 'y': (1, RY), 'z': (2, RZ)}


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
    """the unique nontrivial cycle of a cycle permutation"""
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

# phi: k -> k' with flip(act k vG) = act k' (-2, 1, 3)
_loc = {act(k, (-2, 1, 3)): k for k in range(24)}
PHI = tuple(_loc[tuple(-t if abs(t) == 2 else t for t in act(k, VG))] for k in range(24))
PHI_I = inv(PHI)
for _l in LETTERS:
    assert comp(PHI_I, comp(ROWM[_l], PHI)) == ROWT[_l]
    assert comp(PHI_I, comp(FACE[_l], PHI)) == FACE[_l]
assert comp(PHI_I, comp(COLM, PHI)) == LP


def build_pieces():
    """every conjugate f r f^-1 of a row by a face word, with its cheapest word"""
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


PIECES = build_pieces()
PL = sorted(((v[0], p) for p, v in PIECES.items()), key=lambda t: (t[0], t[1]))


def build_ball():
    """shortest words for every pair of cycles (hKh^-1, hLh^-1) of cost at most LIMIT; the new piece goes on the left"""
    start = (KC, LC)
    dist = {start: (0, None, None)}
    buckets = [[] for _ in range(LIMIT + 1)]
    buckets[0].append(start)
    for w in range(LIMIT + 1):
        for s in buckets[w]:
            if dist[s][0] != w:
                continue
            for pc, p in PL:
                if w + pc > LIMIT:
                    break
                ns = (canon(tuple(p[x] for x in s[0])), canon(tuple(p[x] for x in s[1])))
                o = dist.get(ns)
                if o is None or o[0] > w + pc:
                    dist[ns] = (w + pc, s, p)
                    buckets[w + pc].append(ns)
    return dist


def template_of(dist, s):
    """pieces, leftmost first, each as (face word, row letter)"""
    out = []
    while dist[s][1] is not None:
        _, parent, p = dist[s]
        _, word, rk = PIECES[p]
        out.append((word, rk))
        s = parent
    return out


def template_json(t):
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


class Search:
    def __init__(self):
        self.dist = build_ball()
        print('ball', len(self.dist), flush=True)
        ordered = sorted(self.dist.items(), key=lambda kv: (kv[1][0], kv[0]))
        self.arc_t, self.arc_m = {}, {}      # arc of c (resp. D0) -> states by increasing cost
        for s, v in ordered:
            rec = (v[0], mask(s[0]), mask(s[1]), s)
            for i in range(4):
                self.arc_t.setdefault((s[0][i], s[0][(i + 1) % 4]), []).append(rec)
                self.arc_m.setdefault((s[1][i], s[1][(i + 1) % 4]), []).append(rec)
        self.late_t = {k: [r for r in v if r[3][1] == LC] for k, v in self.arc_t.items()}
        self.late_m = {k: [r for r in v if r[3][0] == KC] for k, v in self.arc_m.items()}
        self.memo = {}

    def pick(self, kind, late, b, x, f, p):
        """cheapest state whose c (or D0) has the arc b -> x, c avoiding f and D0 avoiding p"""
        tab = (self.late_t if late else self.arc_t) if kind == 'T' else (self.late_m if late else self.arc_m)
        for rec in tab.get((b, x), ()):
            if rec[1] & f == 0 and rec[2] & p == 0:
                return rec
        return None

    def level(self, kind, late, b, f, p):
        """(max cost, sum of costs) of a level placing b, with target points f and mirror points p already placed"""
        key = (kind, late, b, f, p)
        if key in self.memo:
            return self.memo[key]
        placed = f if kind == 'T' else p
        mx = tot = 0
        for x in range(24):
            if placed >> x & 1 or x == b:
                continue
            rec = self.pick(kind, late, b, x, f, p)
            if rec is None:
                mx, tot = 99, 10 ** 6
                break
            mx, tot = max(mx, rec[0]), tot + rec[0]
        self.memo[key] = (mx, tot)
        return mx, tot

    def early(self, e, ep):
        """best strictly alternating order T1,M1,...,T5,M5"""
        om_t = KC + (e,)
        om_m = LC + (ep,)

        @functools.lru_cache(None)
        def go(f, p, turn):
            if bin(f).count('1') == 5 and bin(p).count('1') == 5:
                return 0, ()
            best = None
            if turn == 'T':
                for b in om_m:
                    if f >> b & 1:
                        continue
                    mx, t = self.level('T', False, b, f, p)
                    if mx <= LIMIT:
                        r = go(f | 1 << b, p, 'M')
                        if r and (best is None or r[0] + t < best[0]):
                            best = (r[0] + t, (('T', b),) + r[1])
            else:
                for a in om_t:
                    if p >> a & 1:
                        continue
                    mx, t = self.level('M', False, a, f, p)
                    if mx <= LIMIT:
                        r = go(f, p | 1 << a, 'T')
                        if r and (best is None or r[0] + t < best[0]):
                            best = (r[0] + t, (('M', a),) + r[1])
            return best
        return go(0, 0, 'T')

    def order_late(self, kind, z, f0, p0, true_cost):
        """optimal order of the late bases, by a subset DP; arcs only unless true_cost"""
        n = len(z)

        def lvl(b, sub):
            pl = sum(1 << z[i] for i in range(n) if sub >> i & 1)
            if true_cost:
                f, p = (f0 | pl, p0) if kind == 'T' else (f0, p0 | pl)
                return self.level(kind, True, b, f, p)[1]
            # arcs into later base points are counted by arc_cost below; points of the final set are constant
            return sum(self.arc_cost(kind, b, z[i], f0, p0) for i in range(n) if not sub >> i & 1 and z[i] != b)
        best = {0: (0, ())}
        for sub in range(1 << n):
            if sub not in best:
                continue
            base, order = best[sub]
            for i in range(n):
                if sub >> i & 1:
                    continue
                t = base + lvl(z[i], sub)
                ns = sub | 1 << i
                if ns not in best or best[ns][0] > t:
                    best[ns] = (t, order + (z[i],))
        return best[(1 << n) - 1]

    def arc_cost(self, kind, b, x, f, p):
        key = ('arc', kind, b, x, f, p)
        if key not in self.memo:
            rec = self.pick(kind, True, b, x, f, p)
            self.memo[key] = rec[0] if rec else 10 ** 6
        return self.memo[key]

    def factorization(self, base, kind, e, limit=LIMIT, a=5, b=12):
        """least total cost X, Y with X*Y = Alt(base + e), |X| = a, |Y| = b, by enumerating X and exact cover on Y"""
        om = list(base) + [e]
        bi = inv(perm_of(base))
        cost = {}
        for t in itertools.permutations(om, 4):
            if t[0] == min(t):
                s = (t, LC) if kind == 'T' else (KC, t)
                if s in self.dist and self.dist[s][0] <= limit:
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


def raw_entry(dist, s):
    """an entry from a state of common cycles; asserted against evalT and evalTm"""
    t = template_of(dist, s)
    h, hm = eval_on(t, ROWT), eval_on(t, ROWM)
    c = canon(cycle_of(comp(comp(h, COLK), inv(h))))
    d = canon(cycle_of(comp(comp(hm, COLM), inv(hm))))
    assert c == s[0], (c, s)
    assert d == canon(tuple(PHI[x] for x in s[1])), (d, s)
    return dict(template=template_json(t), c=list(c), D=list(d)), t


def e_of(entry):
    """(eT, eM) from the recorded cycles"""
    return comp(perm_of(entry['c']), inv(COLK)), comp(perm_of(entry['D']), inv(COLM))


def main():
    t0 = time.time()
    if '--test-seven' in sys.argv:
        s = Search()
        z = [x for x in range(24) if x not in KC + LC]
        for kind, base in (('T', KC), ('M', LC)):
            for e in z:
                r5 = s.factorization(base, kind, e, limit=7)
                r12 = s.factorization(base, kind, e, limit=7, a=12, b=5)
                print('limit 7', kind, e, '5 x 12:', r5, ' 12 x 5:', r12, flush=True)
        return
    s = Search()
    z = [x for x in range(24) if x not in KC + LC]
    fin_t = {e: s.factorization(KC, 'T', e) for e in z}
    fin_m = {e: s.factorization(LC, 'M', e) for e in z}
    print('final levels', round(time.time() - t0), {e: v and v[0] for e, v in fin_t.items()}, flush=True)
    cands = []
    for e, ep in itertools.permutations(z, 2):
        if not fin_t[e] or not fin_m[ep]:
            continue
        early = s.early(e, ep)
        if not early:
            continue
        zz = [x for x in z if x not in (e, ep)]
        om_t, om_m = mask(KC + (e,)), mask(LC + (ep,))
        tl = s.order_late('T', zz, om_m, om_t, False)[0] + sum(s.arc_cost('T', b, x, om_m, om_t) for b in zz for x in KC + (e,))
        ml = s.order_late('M', zz, om_m, om_t, False)[0] + sum(s.arc_cost('M', b, x, om_m, om_t) for b in zz for x in LC + (ep,))
        cands.append((early[0] + tl + ml + fin_t[e][0] + fin_m[ep][0], e, ep, early[1]))
    cands.sort()
    print('pairs', len(cands), 'best', cands[0][:3], round(time.time() - t0), flush=True)
    _, e, ep, path = cands[0]
    zz = [x for x in z if x not in (e, ep)]
    om_t = mask(KC + (e,))
    om_m = mask(LC + (ep,))
    tl, order_t = s.order_late('T', zz, om_m, om_t, True)
    ml, order_m = s.order_late('M', zz, om_m, om_t, True)
    print('late sums', tl, ml, round(time.time() - t0), flush=True)

    levels = []
    f, p = [], []   # placed target points and placed mirror points, in common coordinates

    def rawp():
        return sorted(PHI[x] for x in p)

    def chain_level(kind, late, b):
        fm, pm = mask(f), mask(p)
        placed = f if kind == 'T' else p
        omega = [x for x in range(24) if x not in placed]
        entries = []
        for x in omega:
            if x == b:
                st = (KC, LC)
            else:
                st = s.pick(kind, late, b, x, fm, pm)[3]
            ent, _ = raw_entry(s.dist, st)
            ent['image'] = x if kind == 'T' else PHI[x]
            entries.append(ent)
        if kind == 'T':
            lv = dict(kind='T', late=late, base=[b], omega=omega)
        else:
            lv = dict(kind='M', late=late, base=[PHI[b]], omega=sorted(PHI[x] for x in omega))
        lv.update(F=sorted(f), P=rawp(), entries=entries)
        levels.append(lv)
        placed.append(b)

    for kind, b in path:
        chain_level(kind, False, b)
    for b in order_t:
        chain_level('T', True, b)
    for b in order_m:
        chain_level('M', True, b)

    def final_level(kind, fin):
        _, xs, ys = fin
        ents = []
        for lst in (xs, ys):
            row = []
            for c in lst:
                st = (canon(c), LC) if kind == 'T' else (KC, canon(c))
                row.append(raw_entry(s.dist, st)[0])
            ents.append(row)
        omega = sorted(set(ents[0][0]['c' if kind == 'T'  else 'D']) | set().union(*[set(q['c' if kind == 'T' else 'D']) for q in ents[1]]))
        assert len(omega) == 5
        chosen = omega[:3]
        table = {}
        for i, a in enumerate(ents[0]):
            for j, b_ in enumerate(ents[1]):
                u = e_of(a)[0 if kind == 'T' else 1]
                v = e_of(b_)[0 if kind == 'T' else 1]
                g = comp(u, v)
                key = tuple(g[q] for q in chosen)
                assert key not in table
                table[key] = (i, j)
        assert len(table) == 60
        levels.append(dict(kind=kind + '-final', base=chosen, omega=omega, F=sorted(f), P=rawp(), X=ents[0], Y=ents[1],
                           table=[[list(k), v[0], v[1]] for k, v in sorted(table.items())]))
        (f if kind == 'T' else p).extend(omega if kind == 'T' else [PHI_I[x] for x in omega])

    final_level('T', fin_t[e])
    final_level('M', fin_m[ep])

    sizes = []
    lens = []
    for lv in levels:
        if 'entries' in lv:
            sizes.append(len(lv['entries']))
            lens += [tl_(q) for q in lv['entries']]
        else:
            sizes += [len(lv['X']), len(lv['Y'])]
            lens += [tl_(q) for q in lv['X'] + lv['Y']]
    out = dict(format='exact-chain-v1', K_cycle=list(KC), M_cycle=list(canon(cycle_of(COLM))), L_common_cycle=list(LC),
               phi=list(PHI), e_target=e, e_mirror=ep, sizes=sizes, L=max(lens), total_moves=sum(lens), levels=levels)
    fn = os.path.join(HERE, 'exact_chain.json')
    with open(fn, 'w') as fh:
        json.dump(out, fh, separators=(',', ':'))
    print('sizes', sizes)
    print('order', [lv['kind'] + ('*' if lv.get('late') else '') + str(lv['base']) for lv in levels])
    print('e', e, 'ep', ep, 'L', out['L'], 'total moves', out['total_moves'], 'entries', len(lens), 'wrote', fn, 't', round(time.time() - t0))


def tl_(entry):
    return sum(2 * len(f) + 1 for f, _ in entry['template'])


if __name__ == '__main__':
    main()
