#!/usr/bin/env python3
"""Evaluate the word-length formulas proved in Lean, with the best parameters per n. Nothing here is part of a proof.

Formulas (r = n//2 - 1):
  upperW (old, Solve.lean)        3n+406+275*(r//s+1)*((2s+4)2^s+2(n-n//2))
  exactW (ExactCost.lean)         3n+406+2200 r (S+2)+R*(r^2//S+2(r//S+1)Cslot), R=sum(S//2//s_m+1), Cslot>=m^s_m*(2 s_m*8)
  colouredW (ColouredCost.lean)   same, with (m,w) keys; Tb>=(m/w)^s*(ln n+1)+1, Cslot>=Tb*(2 s L)
  trie variants (TrieCost.lean)   Cslot>=m^s*(4*8) [uniform], or per-list cost 2*w*(1+m+...+m^(s-1)), w=sum of template lengths
Lower bounds: LowerCommute.lean, in htm (d=2.89) and qtm (d=2.33).
trieM and bad=700 are unproved estimates of possible improvements; everything else is a proved formula.
Usage: uv run python scripts/constants_exact.py
"""
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ex = json.load(open(os.path.join(HERE, 'exact_chain.json')))


def tlen(t):
    return sum(2 * len(p[0]) + 1 for p in t)


def level_entries(l):
    if 'entries' in l:
        return [e['template'] for e in l['entries']]
    raise KeyError(list(l.keys()))


MS = ex['sizes']
assert math.prod(MS) == (math.factorial(24) // 2) ** 2
LE = math.log2(math.factorial(24) // 2)
LAM = 2 * LE
LZ = math.log2(math.factorial(24) // 24 ** 6)

COL_KEYS = [(24, 4), (24, 4), (23, 4), (23, 4), (22, 4), (22, 4), (21, 4), (21, 4), (20, 3), (20, 3), (19, 4), (18, 4), (17, 3), (16, 3),
            (15, 3), (14, 2), (13, 1), (12, 2), (11, 2), (10, 2), (9, 1), (8, 3), (7, 3), (6, 2), (19, 4), (18, 3), (17, 4), (16, 3), (15, 3),
            (14, 2), (13, 3), (12, 3), (11, 1), (10, 2), (9, 1), (8, 2), (7, 2), (6, 2), (12, 1), (5, 1), (12, 1), (5, 1)]
COL_L = 8


def list_weights():
    """Per-list (m, w, trie-of-moves size), from the JSON; the order is that of `sizes`."""
    out = []
    for l in ex['levels']:
        tm = []
        if 'entries' in l:
            tm = [l['entries']]
        else:
            tm = [l[k] for k in l if isinstance(l[k], list) and l[k] and isinstance(l[k][0], dict) and 'template' in l[k][0]]
        for ents in tm:
            ts = [e['template'] for e in ents]
            nodes = set()
            for t in ts:
                mv = []
                for f, c in t:
                    ff = [tuple(a) for a in f]
                    mv += [('f',) + a for a in ff] + [('r',) + tuple(c)] + [('g',) + a for a in reversed(ff)]
                for k in range(1, len(mv) + 1):
                    nodes.add(tuple(mv[:k]))
            out.append((len(ts), sum(tlen(t) for t in ts), len(nodes)))
    return out


WEIGHTS = list_weights()
assert sorted(w[0] for w in WEIGHTS) == sorted(MS), (len(WEIGHTS), len(MS))


# ---- old
def upperW(n, s):
    r = n // 2 - 1
    return 3 * n + 406 + 275 * ((r // s + 1) * ((2 * s + 4) * 2 ** s + 2 * (n - n // 2)))


def best_old(n):
    x = n.bit_length()
    lo = max(1, x - int(3 * math.log2(x)) - 10)
    return min((upperW(n, s), s) for s in range(lo, x + 2))


# ---- exact, general evaluator: lists of (s, cost of one job); the Lean bound with a uniform Cslot takes the max
def exact_terms(n, S, ss, Cslot=None, costs=None, bad=2200):
    r = n // 2 - 1
    A = S // 2
    base = 3 * n + 406
    badterm = bad * (r * (S + 2))
    R = sum(A // s + 1 for s in ss)
    col = R * (r ** 2 // S)
    if costs is None:
        slots = R * (2 * (r // S + 1) * Cslot)
    else:
        slots = sum((A // s + 1) * (2 * (r // S + 1) * c) for s, c in zip(ss, costs))
    return base, badterm, col, slots


def geom(m, s):
    return (m ** s - 1) // (m - 1)


def s_grid(n):
    r = n // 2 - 1
    g = max(1, math.isqrt(42 * max(r, 1) // 2200))
    out = set()
    # very large n: only near the optimum
    if n.bit_length() > 200:
        out = {2 * max(1, (g * 13 ** (e + 6)) // 10 ** (e + 6) if e >= -6 else g) for e in range(-6, 7)}
        out = {2 * max(1, g * (1 << (e + 6)) // 64) for e in range(-6, 7)}
        return sorted(out)
    v = 2.0
    while v < 4 * n:
        out.add(int(v) // 2 * 2 or 2)
        v *= 1.15
    return sorted(out)


def beta_window(n, wide=False):
    x = n.bit_length()
    lx = math.log2(x)
    lo = max(0.0, x - 3.2 * lx - 28)
    hi = x + 1
    step = 0.5 if x > 64 else 0.25
    if x > 200 and not wide:
        lo = x - 3.2 * lx - 12
        hi = x - lx + 2
    v = lo
    while v <= hi:
        yield v
        v += step


def max_s(m, beta):
    return max(1, int(beta / math.log2(m) + 1e-12))


def best_exact(n):
    """exactW: uniform Cslot = max m^s (2 s 8)."""
    best = None
    seen = set()
    x = n.bit_length()
    for beta in beta_window(n):
        ss = [max_s(m, beta) for m in MS]
        key = tuple(ss)
        if key in seen:
            continue
        seen.add(key)
        C = max(m ** s * (2 * s * 8) for m, s in zip(MS, ss))
        # enlarge each s while it fits under the same C
        ss2 = []
        for m, s in zip(MS, ss):
            while m ** (s + 1) * (2 * (s + 1) * 8) <= C:
                s += 1
            ss2.append(s)
        for S in s_grid(n):
            t = exact_terms(n, S, ss2, Cslot=C)
            w = sum(t)
            if best is None or w < best[0]:
                best = (w, S, beta, t)
    return best


def best_trie_uniform(n):
    """Trie slots, global Cslot >= m^s * (4 * 8), same formula otherwise."""
    best = None
    seen = set()
    for beta in beta_window(n):
        ss = [max_s(m, beta) for m in MS]
        key = tuple(ss)
        if key in seen:
            continue
        seen.add(key)
        C = max(m ** s * 32 for m, s in zip(MS, ss))
        ss2 = []
        for m, s in zip(MS, ss):
            while m ** (s + 1) * 32 <= C:
                s += 1
            ss2.append(s)
        for S in s_grid(n):
            t = exact_terms(n, S, ss2, Cslot=C)
            w = sum(t)
            if best is None or w < best[0]:
                best = (w, S, beta, t)
    return best


def best_trie_perlist(n, weight=1, bad=2200):
    """Trie slots, per-list s and job cost 2 w (1+m+...+m^(s-1)); weight=2 uses the move-level trie size instead of w."""
    r = n // 2 - 1
    best = None
    x = n.bit_length()
    for S in s_grid(n):
        A = S // 2
        ss, costs = [], []
        for (m, w, tr) in WEIGHTS:
            ww = w if weight == 1 else tr
            s0 = max(1, int((x - math.log2(x) - 12) / math.log2(m)))
            bestl = None
            for s in range(max(1, s0 - 6), s0 + 8):
                c = 2 * ww * geom(m, s)
                val = (A // s + 1) * (r ** 2 // S + 2 * (r // S + 1) * c)
                if bestl is None or val < bestl[0]:
                    bestl = (val, s, c)
            ss.append(bestl[1])
            costs.append(bestl[2])
        t = exact_terms(n, S, ss, costs=costs, bad=bad)
        w = sum(t)
        if best is None or w < best[0]:
            best = (w, S, None, t)
    return best


def best_coloured(n):
    """colouredW, ParamsOK with Tb = ceil((m/w)^s (ln n + 1)) + 1, Cslot = max Tb 2 s L."""
    best = None
    seen = set()
    x = n.bit_length()
    # ln n + 1, as an exact rational upper bound
    lnn = math.log(n) + 1 + 1e-9
    for beta in beta_window(n, wide=True):
        ss = [max(1, int(beta / (math.log2(m) - math.log2(w)) + 1e-12)) for m, w in COL_KEYS]
        key = tuple(ss)
        if key in seen:
            continue
        seen.add(key)
        C = 0
        for (m, w), s in zip(COL_KEYS, ss):
            tb = (m ** s * int(lnn * 2 ** 40)) // (w ** s * 2 ** 40) + 2
            C = max(C, tb * (2 * s * COL_L))
        for S in s_grid(n):
            t = exact_terms(n, S, ss, Cslot=C)
            w_ = sum(t)
            if best is None or w_ < best[0]:
                best = (w_, S, beta, t)
    return best


def lg(n):
    return math.log2(n)


def lower_lab(n, d):
    return (19.509 * (n + 1) * (n - 3) - 1) / (lg(n) + d) if n < 2 ** 900 else None


def ratio_lab(n, w, d):
    """upper/lower, for big n, exactly enough."""
    return w * (lg(n) + d) / (19.509 * (n + 1) * (n - 3) - 1) if n < 2 ** 900 else (w * 2 ** 40 // ((19509 * (n + 1) * (n - 3) - 1000) * 2 ** 40 // 1000)) and (
        (w * 2 ** 60 // (n * n)) / 2 ** 60 * (lg(n) + d) / 19.509)


def ratio_col(n, w, d):
    return (w * 2 ** 60 // (n * n)) / 2 ** 60 * (lg(n) + d) / 12.88


def rel(n, w):
    """w lg n / n^2."""
    return (w * 2 ** 60 // (n * n)) / 2 ** 60 * lg(n)


def fmt(n):
    if n < 10 ** 13:
        return str(n)
    return '2^%d' % round(lg(n))


POINTS = [100, 200, 500, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8, 10 ** 9, 10 ** 10, 10 ** 11, 10 ** 12, 2 ** 48, 2 ** 64, 2 ** 80, 2 ** 100, 2 ** 200,
          2 ** 500, 2 ** 1000, 2 ** 2000, 2 ** 5000, 2 ** 10000]


def main():
    print('Lambda/8 = %.4f, lgZ/4 = %.4f' % (LAM / 8, LZ / 4))
    print('%8s | %8s %8s %8s %8s %8s | %6s %6s %6s %6s| %6s' % ('n', 'old', 'exact', 'trieU', 'trieL', 'trieM', 'r_old', 'r_ex', 'r_trU', 'r_trL', 'colW'))
    rows = []
    for n in POINTS:
        o = best_old(n)
        e = best_exact(n)
        tu = best_trie_uniform(n)
        tl = best_trie_perlist(n)
        tm = best_trie_perlist(n, weight=2)
        c = best_coloured(n)
        d = 2.89
        print('%8s | %8.1f %8.1f %8.1f %8.1f %8.1f | %6.2f %6.2f %6.2f %6.2f| %6.1f' % (
            fmt(n), rel(n, o[0]), rel(n, e[0]), rel(n, tu[0]), rel(n, tl[0]), rel(n, tm[0]),
            ratio_col(n, o[0], d) * 12.88 / 19.509, ratio_col(n, e[0], d) * 12.88 / 19.509,
            ratio_col(n, tu[0], d) * 12.88 / 19.509, ratio_col(n, tl[0], d) * 12.88 / 19.509, rel(n, c[0])))
        rows.append((n, o, e, tu, tl, tm, c))
    print('\ncoloured: upper/lower (min of colouredW and exactW and upperW)')
    for n, o, e, tu, tl, tm, c in rows:
        u = min(o[0], e[0], c[0])
        print('%8s colW/n2lg %8.1f  best/lower %7.2f   (bestLabelled-trie/lower %7.2f)' % (fmt(n), rel(n, c[0]), ratio_col(n, u, 2.89), ratio_col(n, min(u, tl[0]), 2.89)))
    print('\nterm shares of exactW (base, bad-orbit, column, slot); S, beta; second order D_eff = (Lambda/8) n^2 / W')
    for n, o, e, tu, tl, tm, c in rows:
        for name, b in (('exact', e), ('trieL', tl)):
            w, S, beta, t = b
            D = (LAM / 8) / (w * 2 ** 60 // (n * n)) * 2 ** 60 if w * 2 ** 60 // (n * n) else 0
            x = lg(n)
            S = S if S < 10 ** 9 else '2^%d' % round(math.log2(S))
            beta = '-' if beta is None else '%.1f' % beta
            print('%8s %6s S=%-12s beta=%-8s base %.3f bad %.3f col %.3f slot %.3f D=%.2f  lg n-D=%.2f  c1=lg n-lglg n-D=%.2f  c3=lg n-3lglg n-D=%.2f' % (
                fmt(n), name, S, beta, t[0] / w, t[1] / w, t[2] / w, t[3] / w, D, x - D, x - math.log2(x) - D, x - 3 * math.log2(x) - D))
    # crossover old/new
    print('\ncrossover exactW < upperW; trie variants < upperW:')
    for name, fn in (('exact', best_exact), ('trieU', best_trie_uniform), ('trieL', best_trie_perlist)):
        lo, hi = 100, 10 ** 15
        if fn(lo)[0] < best_old(lo)[0]:
            print(name, 'already at 100')
            continue
        # scan geometric, then bisect at the last sign change
        grid = [int(100 * 1.25 ** k) for k in range(0, 135)]
        last = None
        for a, b in zip(grid, grid[1:]):
            if fn(a)[0] >= best_old(a)[0] and fn(b)[0] < best_old(b)[0]:
                last = (a, b)
        if last is None:
            print(name, 'no crossover found below', grid[-1])
            continue
        a, b = last
        while b - a > max(1, a // 200):
            mid = (a + b) // 2
            if fn(mid)[0] < best_old(mid)[0]:
                b = mid
            else:
                a = mid
        print(name, 'beats old for n >=~ %d (2^%.2f)' % (b, lg(b)))
    # one-at-a-time gains
    print('\nimprovements at given n: W ratio to exactW-best')
    for n in (10 ** 3, 10 ** 4, 10 ** 6, 10 ** 9, 10 ** 12, 2 ** 64, 2 ** 100, 2 ** 1000):
        e = best_exact(n)[0]
        tu = best_trie_uniform(n)[0]
        tl = best_trie_perlist(n)[0]
        tm = best_trie_perlist(n, weight=2)[0]
        b1 = best_trie_perlist(n, bad=700)[0]
        print('%8s old/ex %.3f | trieU/ex %.3f | trieL/ex %.3f | trieMoves/ex %.3f | trieL with bad=700 /ex %.3f' % (fmt(n), best_old(n)[0] / e, tu / e, tl / e, tm / e, b1 / e))


if __name__ == '__main__':
    main()
