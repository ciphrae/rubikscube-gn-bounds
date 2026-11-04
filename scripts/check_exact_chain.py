"""Independent verifier of scripts/exact_chain.json. Shares no code with scripts/exact_chain.py.

All permutations are recomputed from the templates, using scripts/rot.py and the definitions of RubiksGN/PassAction.lean.
Exit status is nonzero on any failure.

Usage: uv run python scripts/check_exact_chain.py [file]          verify a file (default scripts/exact_chain.json)
       uv run python scripts/check_exact_chain.py --corrupt-test  also confirm that corrupted copies are rejected
"""
import copy
import itertools
import json
import math
import os
import random
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SCRIPTS)
import rot


class Fail(Exception):
    pass


def need(ok, *msg):
    if not ok:
        raise Fail(' '.join(map(str, msg)))


def prod(*ps):
    """(p1 * p2 * ...)(k) = p1(p2(...(k)))"""
    out = list(range(24))
    for p in reversed(ps):
        out = [p[v] for v in out]
    return tuple(out)


def inverse(p):
    q = [None] * 24
    for i in range(24):
        q[p[i]] = i
    return tuple(q)


IDENT = tuple(range(24))
COORD = {'x': 0, 'y': 1, 'z': 2}
RX = {'x': rot.RX, 'y': rot.RY, 'z': rot.RZ}


def layer(axis, value):
    """genP: the rotation about axis on the stickers act k (-1,2,3) whose coordinate is value"""
    res = []
    for k in range(24):
        res.append(rot.mul(RX[axis], k) if rot.act(k, (-1, 2, 3))[COORD[axis]] == value else k)
    return tuple(res)


def letter_perm(letter, magnitude):
    axis, side, direction = letter
    p = layer(axis, magnitude if side else -magnitude)
    return p if direction else inverse(p)


COLK = layer('x', 2)
COLM = layer('x', 1)
# the literal sanity checks of RubiksGN/PassAction.lean
need(list(COLK) == [0, 1, 2, 3, 4, 13, 6, 7, 8, 9, 10, 11, 12, 21, 14, 15, 16, 17, 18, 5, 20, 19, 22, 23], 'colK')
need(list(COLM) == [0, 1, 2, 3, 4, 5, 6, 16, 8, 9, 14, 11, 12, 13, 7, 15, 10, 17, 18, 19, 20, 21, 22, 23], 'colM')
need(list(letter_perm(('y', False, True), 1)) == [0, 1, 2, 6, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19, 3, 21, 22, 23], 'rowT y')
need(list(letter_perm(('z', True, True), 1)) == [0, 1, 8, 3, 4, 2, 6, 7, 12, 9, 10, 11, 5, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], 'rowT z')
need(list(letter_perm(('y', False, True), 2)) == [0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 15, 11, 10, 13, 14, 4, 16, 17, 18, 19, 20, 21, 22, 23], 'rowM y')
need(list(letter_perm(('z', True, True), 2)) == [0, 6, 2, 3, 4, 5, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15, 23, 17, 18, 19, 20, 21, 22, 1], 'rowM z')
need(list(letter_perm(('z', True, True), 3)) == [3, 1, 2, 10, 4, 5, 6, 7, 8, 9, 19, 11, 12, 13, 14, 15, 16, 17, 18, 0, 20, 21, 22, 23], 'face z')
need(list(letter_perm(('z', False, False), 3)) == [0, 1, 2, 3, 18, 5, 6, 13, 8, 9, 10, 11, 12, 4, 14, 15, 16, 17, 7, 19, 20, 21, 22, 23], 'face z-')


def parse_letter(l):
    need(isinstance(l, list) and len(l) == 3 and l[0] in COORD and isinstance(l[1], bool) and isinstance(l[2], bool), 'letter', l)
    return tuple(l)


def eval_template(tmpl, magnitude):
    """evalT for magnitude 1, evalTm for magnitude 2: the product of f r f^-1, first piece leftmost"""
    h = IDENT
    for f, r in tmpl:
        fv = IDENT
        for l in f:
            fv = prod(fv, letter_perm(parse_letter(l), 3))
        h = prod(h, fv, letter_perm(parse_letter(r), magnitude), inverse(fv))
    return h


def tmpl_len(tmpl):
    return sum(2 * len(f) + 1 for f, _ in tmpl)


def four_cycle(p, name):
    """the 4-cycle of p as a list starting at its least point"""
    moved = [k for k in range(24) if p[k] != k]
    need(len(moved) == 4, name, 'is not a 4-cycle', moved)
    out = [moved[0]]
    while p[out[-1]] != moved[0]:
        out.append(p[out[-1]])
    need(len(out) == 4, name, 'is not a 4-cycle', out)
    return out


def elements(entry):
    """recompute (eT, eM) from the template, and check the recorded cycles"""
    t = entry['template']
    h = eval_template(t, 1)
    hm = eval_template(t, 2)
    conj_t = prod(h, COLK, inverse(h))
    conj_m = prod(hm, COLM, inverse(hm))
    need(four_cycle(conj_t, 'conjT') == entry['c'], 'recorded c', entry['c'], four_cycle(conj_t, 'conjT'))
    need(four_cycle(conj_m, 'conjM') == entry['D'], 'recorded D', entry['D'], four_cycle(conj_m, 'conjM'))
    return prod(conj_t, inverse(COLK)), prod(conj_m, inverse(COLM))


def fixes(p, pts):
    return all(p[x] == x for x in pts)


def parity(perm, pts):
    idx = {x: i for i, x in enumerate(pts)}
    arr = [idx[perm[x]] for x in pts]
    return sum(1 for i in range(len(arr)) for j in range(i) if arr[j] > arr[i]) % 2


def check_chain_level(lv, tag):
    """a level of kind T or M: the entries fix what is placed, and one entry for each image of the base point"""
    kind = lv['kind']
    b = lv['base']
    need(len(b) == 1, tag, 'one base point')
    b = b[0]
    placed = lv['F'] if kind == 'T' else lv['P']
    omega = sorted(set(range(24)) - set(placed))
    need(lv['omega'] == omega, tag, 'omega')
    need(b in omega, tag, 'base is already placed')
    seen = {}
    for ent in lv['entries']:
        et, em = elements(ent)
        need(fixes(et, lv['F']), tag, 'target element moves a placed point')
        need(fixes(em, lv['P']), tag, 'mirror element moves a placed point')
        if lv.get('late'):
            need((em if kind == 'T' else et) == IDENT, tag, 'late level, other element is not 1')
        img = (et if kind == 'T' else em)[b]
        need(ent['image'] == img, tag, 'recorded image')
        need(img not in seen, tag, 'duplicate image', img)
        seen[img] = (et, em)
    need(sorted(seen) == omega, tag, 'images do not cover omega')
    need(len(lv['entries']) == len(omega), tag, 'size')
    return seen


def check_final_level(lv, tag):
    kind = lv['kind'][0]
    omega = lv['omega']
    need(len(omega) == 5 and len(lv['base']) == 3 and set(lv['base']) <= set(omega), tag, 'omega, base')
    placed = lv['F'] if kind == 'T' else lv['P']
    need(sorted(placed) == sorted(set(range(24)) - set(omega)), tag, 'placed is the complement of omega')
    need(len(lv['X']) == 5 and len(lv['Y']) == 12, tag, 'sizes')

    def els(lst):
        out = []
        for ent in lst:
            et, em = elements(ent)
            need(fixes(et, lv['F']) and fixes(em, lv['P']), tag, 'entry moves a placed point')
            need((em if kind == 'T' else et) == IDENT, tag, 'other element is not 1')
            out.append(et if kind == 'T' else em)
        return out
    xs, ys = els(lv['X']), els(lv['Y'])
    table = {}
    for key, i, j in lv['table']:
        need(tuple(key) not in table, tag, 'duplicate key')
        need(0 <= i < 5 and 0 <= j < 12, tag, 'table index')
        table[tuple(key)] = (i, j)
    need(len(table) == 60, tag, 'table size')
    prods = set()
    n_even = 0
    for images in itertools.permutations(omega):
        g = list(range(24))
        for a, v in zip(omega, images):
            g[a] = v
        g = tuple(g)
        if parity(g, omega):
            continue
        n_even += 1
        key = tuple(g[a] for a in lv['base'])
        need(key in table, tag, 'no witness for', key)
        i, j = table[key]
        need(prod(xs[i], ys[j]) == g, tag, 'wrong witness', key)
        prods.add((i, j))
    need(n_even == 60 and len(prods) == 60, tag, 'witnesses are not a bijection')
    return xs, ys, table


def verify(data, trials=2000, seed=20261104):
    need(data.get('format') == 'exact-chain-v1', 'format')
    levels = data['levels']
    kinds = [lv['kind'] for lv in levels]
    need(kinds.count('T-final') == 1 and kinds.count('M-final') == 1, 'one final level per chain')
    # placed points follow from the order of the levels
    f, p = [], []
    sizes = []
    built = []
    maxlen = total = 0
    for n, lv in enumerate(levels):
        tag = f'level {n} {lv["kind"]} {lv["base"]}:'
        need(lv['F'] == sorted(f) and lv['P'] == sorted(p), tag, 'F or P is not what the earlier levels placed')
        if lv['kind'] in ('T', 'M'):
            built.append((lv['kind'], lv['base'][0], check_chain_level(lv, tag)))
            (f if lv['kind'] == 'T' else p).append(lv['base'][0])
            sizes.append(len(lv['entries']))
            ents = lv['entries']
        else:
            need(lv['kind'] in ('T-final', 'M-final'), tag, 'unknown kind')
            built.append((lv['kind'], lv['base'], check_final_level(lv, tag)))
            sizes += [len(lv['X']), len(lv['Y'])]
            ents = lv['X'] + lv['Y']
            (f if lv['kind'][0] == 'T' else p).extend(lv['omega'])
        for e in ents:
            maxlen = max(maxlen, tmpl_len(e['template']))
            total += tmpl_len(e['template'])
    need(sorted(f) == list(range(24)) and sorted(p) == list(range(24)), 'a chain does not finish')
    need(len(sizes) == 42, 'number of lists', len(sizes))
    need(sizes == data['sizes'], 'recorded sizes')
    want = sorted(2 * (list(range(6, 25)) + [5, 12]))
    need(sorted(sizes) == want, 'list sizes', sorted(sizes))
    need(math.prod(sizes) == (math.factorial(24) // 2) ** 2, 'product of the sizes')
    need(data['L'] == maxlen and data['total_moves'] == total, 'recorded L or total', maxlen, total)

    # end to end, by the level procedure, with the raw products recomputed from the templates
    rng = random.Random(seed)

    def even_perm():
        while True:
            q = list(range(24))
            rng.shuffle(q)
            if parity(q, list(range(24))) == 0:
                return tuple(q)
    for trial in range(trials):
        tgt, mir = even_perm(), even_perm()
        r_t, r_m = tgt, mir
        chosen = []
        for lv, (kind, base, tab) in zip(levels, built):
            if kind in ('T', 'M'):
                key = (r_t if kind == 'T' else r_m)[base]
                need(key in tab, 'procedure: no entry', kind, base, key)
                pos = [i for i, ent in enumerate(lv['entries']) if ent['image'] == key]
                need(len(pos) == 1, 'procedure: entry', pos)
                steps = [lv['entries'][pos[0]]]
            else:
                xs, ys, table = tab
                r = r_t if kind == 'T-final' else r_m
                i, j = table[tuple(r[a] for a in base)]
                steps = [lv['X'][i], lv['Y'][j]]
            for ent in steps:
                et, em = elements_cached(ent)
                r_t = prod(inverse(et), r_t)
                r_m = prod(inverse(em), r_m)
                chosen.append((et, em))
        need(r_t == IDENT and r_m == IDENT, 'procedure: residual is not 1')
        pt, pm = IDENT, IDENT
        for et, em in chosen:
            pt, pm = prod(pt, et), prod(pm, em)
        need(pt == tgt and pm == mir, 'procedure: product is wrong')
        need(len(chosen) == 42, 'procedure: number of choices')
    return dict(sizes=sizes, L=maxlen, total=total, trials=trials)


_CACHE = {}


def elements_cached(ent):
    key = id(ent)
    if key not in _CACHE:
        _CACHE[key] = (ent, elements(ent))
    return _CACHE[key][1]


def corruptions(data):
    """copies of the data, each corrupted once"""
    rng = random.Random(1)

    def fresh():
        return copy.deepcopy(data)

    def some_entry(d, nonempty=True):
        while True:
            lv = rng.choice(d['levels'])
            lst = lv.get('entries') or rng.choice([lv.get('X'), lv.get('Y')])
            e = rng.choice(lst)
            if e['template'] or not nonempty:
                return lv, lst, e
    d = fresh()
    _, _, e = some_entry(d)
    e['template'][0][1][2] = not e['template'][0][1][2]
    yield 'flip a row direction', d
    d = fresh()
    _, _, e = some_entry(d)
    e['template'][0][1][0] = {'x': 'y', 'y': 'z', 'z': 'x'}[e['template'][0][1][0]]
    yield 'change a row axis', d
    d = fresh()
    _, _, e = some_entry(d)
    e['c'] = e['c'][:1] + e['c'][1:][::-1]
    yield 'reverse a recorded cycle', d
    d = fresh()
    next(lv for lv in d['levels'] if lv['kind'] == 'T')['entries'].pop(3)
    yield 'drop an entry', d
    d = fresh()
    lv = next(lv for lv in d['levels'] if lv['kind'] == 'T-final')
    lv['table'][0][1], lv['table'][1][1] = lv['table'][1][1], (lv['table'][0][1] + 1) % 5
    yield 'change a witness', d
    d = fresh()
    d['levels'][12]['F'] = d['levels'][12]['F'][1:]
    yield 'forget a placed point', d
    d = fresh()
    d['levels'][3], d['levels'][4] = d['levels'][4], d['levels'][3]
    yield 'swap two levels', d
    d = fresh()
    a = next(lv for lv in d['levels'] if lv['kind'] == 'M' and lv.get('late'))['entries']
    a[0], a[1] = dict(a[1], image=a[0]['image']), dict(a[0], image=a[1]['image'])
    yield 'swap the images of two entries', d


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    fn = args[0] if args else os.path.join(SCRIPTS, 'exact_chain.json')
    with open(fn) as fh:
        data = json.load(fh)
    res = verify(data)
    print('OK', fn)
    print(' lists', len(res['sizes']), 'sizes', res['sizes'])
    print(' product of sizes = (24!/2)^2')
    print(' log2 of product =', round(sum(math.log2(m) for m in res['sizes']), 6), ' 2 log2(24!/2) =',
          round(2 * math.log2(math.factorial(24) // 2), 6))
    print(' L', res['L'], 'total moves', res['total'], 'random pairs factorized', res['trials'])
    if '--corrupt-test' in sys.argv:
        for name, bad in corruptions(data):
            try:
                verify(bad, trials=5)
            except (Fail, KeyError, IndexError, StopIteration) as ex:
                print(' corruption rejected:', name, '--', str(ex)[:70])
            else:
                raise Fail('corruption was accepted: ' + name)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Fail as ex:
        print('FAILED:', ex)
        sys.exit(1)
