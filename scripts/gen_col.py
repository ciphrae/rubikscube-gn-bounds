"""Write RubiksGN/ColourData.lean from scripts/chain_col3.json, which is built here from scripts/chain_col2.json.

`ColourData.check` asks both families to have the same keys `(m, w)`, level by level. The families of chain_col2.json do not
(their base orders differ, and E plays the final lists in the other order). So family O is kept as it is and family E is
rebuilt: same base positions in the same order as O, hence the same keys; final levels played 12 first, 5 second, which needs
A * B = Alt(Omega) with |A| = 12, |B| = 5, for E plays R = (eT b)^-1 (eT a)^-1 = (eT a * eT b)^-1.

Verify the result independently with `uv run python scripts/check_chain_col2.py scripts/chain_col3.json`.
Also writes RubiksGN/ColourCheck.lean, the kernel check, one theorem per step: a single `decide +kernel` on the whole of
`ColourData.check` works, in 2.5 minutes, but it peaks at 24 GB, whereas the kernel's caches are freed between declarations.
Usage: uv run python scripts/gen_col.py [--rebuild]
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import chain_col2 as cc

SRC = os.path.join(HERE, 'chain_col2.json')
DST = os.path.join(HERE, 'chain_col3.json')
OUT = os.path.join(HERE, '..', 'RubiksGN', 'ColourData.lean')
OUT_CHECK = os.path.join(HERE, '..', 'RubiksGN', 'ColourCheck.lean')


def reversed_factorization(srch, base, kind, e, a=12, b=5):
    """least total cost A, B with A * B = Alt(base + e), both lists of elements c P^-1 with the other element 1"""
    om = list(base) + [e]
    bi = cc.inv(cc.perm_of(base))
    cost = {}
    for t in itertools.permutations(om, 4):
        if t[0] == min(t):
            s = (t, cc.LC) if kind == 'T' else (cc.KC, t)
            if s in srch.dist:
                cost[t] = srch.dist[s][0]
    cs = sorted(cost)
    els = [cc.comp(cc.perm_of(c), bi) for c in cs]
    ids = {}
    n = len(els)
    m = [[ids.setdefault(cc.comp(els[i], els[j]), len(ids)) for j in range(n)] for i in range(n)]
    w = [cost[c] for c in cs]
    sw = sorted(w)
    best = None
    full = (1 << 60) - 1
    for y in itertools.combinations(range(n), b):
        sy = sum(w[i] for i in y)
        if best is not None and sy + sum(sw[:a]) >= best[0]:
            continue
        fps = []
        for j in range(n):
            fp = 0
            for i in y:
                if fp >> m[j][i] & 1:
                    fp = None
                    break
                fp |= 1 << m[j][i]
            if fp is not None:
                fps.append((w[j], fp, j))
        if len(fps) < a:
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
            if len(sol) == a:
                if best is None or sy + s < best[0]:
                    best = (sy + s, tuple(sol), y)
                return
            if best is not None and sy + s + (a - len(sol)) * sw[0] >= best[0]:
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


def rebuild_e(srch, src):
    e_t, e_m = src['e_target'], src['e_mirror_common']
    levels = []
    f, p = 0, 0
    o_levels = src['families']['O']['time_order_levels']
    for n, lv in enumerate(o_levels):
        if lv['kind'] != 'place':
            continue
        kind = lv['orbit']
        b = lv['base'] if kind == 'T' else cc.PHI_I[lv['base']]
        late = n >= 10
        ents = []
        for x in range(24):
            if (f if kind == 'T' else p) >> x & 1:
                continue
            if x == b:
                s = (cc.KC, cc.LC)
            else:
                rec = srch.pick('E', kind, late, b, x, f, p)
                assert rec is not None, f'no entry: level {n}, kind {kind}, base {b}, position {x}'
                s = rec[3]
            tj, _ = cc.entry(srch, s, 'E')
            ents.append({'position': x if kind == 'T' else cc.PHI[x], 'template': tj})
        levels.append({'orbit': kind, 'kind': 'place', 'base': lv['base'], 'w': lv['w'], 'entries': ents})
        if kind == 'T':
            f |= 1 << b
        else:
            p |= 1 << b
    for kind, base, e in (('T', cc.KC, e_t), ('M', cc.LC, e_m)):
        r = reversed_factorization(srch, base, kind, e)
        assert r, 'no factorization'
        print('final', kind, 'cost', r[0], flush=True)
        for lst, nm in ((r[1], 'A'), (r[2], 'B')):
            ents = []
            for c in lst:
                s = (c, cc.LC) if kind == 'T' else (cc.KC, c)
                tj, _ = cc.entry(srch, s, 'E')
                ents.append({'template': tj})
            levels.append({'orbit': kind, 'kind': 'final' + nm, 'w': 1, 'entries': ents})
    return levels


def build_json():
    with open(SRC) as fh:
        src = json.load(fh)
    srch = cc.Search(8)
    src['families']['E'] = {'time_order_levels': rebuild_e(srch, src)}
    src['format'] = 'chain-col3-v1'
    src['statement'] += ('\n\nchain-col3: family O is that of chain_col2.json. Family E is rebuilt by scripts/gen_col.py with the bases of O, '
                         'so both have the same keys (m, w) level by level; its final levels are A (12) then B (5), with A * B = Alt(Omega) in eT.')
    with open(DST, 'w') as fh:
        json.dump(src, fh, separators=(',', ':'))
    print('written', os.path.normpath(DST), os.path.getsize(DST), flush=True)


HEADER = """import RubiksGN.SolveColoured

/-!
# The colour lists

Generated by `scripts/gen_col.py` from `scripts/chain_col3.json`. Do not edit. Family `O` is that of `scripts/chain_col2.json`;
family `E` is rebuilt with the same bases, so that both have the same keys. Both are verified by `scripts/check_chain_col2.py`.

`colO k`, `colE k` are the steps of the families, in time order. Bases are raw coordinates of their orbit.
-/

namespace RubiksGN
"""


def b(v):
    return 'true' if v else 'false'


def letter(l):
    return f'(.{l[0]}, {b(l[1])}, {b(l[2])})'


def tmpl(t):
    return '[' + ', '.join('⟨[' + ', '.join(letter(l) for l in f) + '], ' + letter(r) + '⟩' for f, r in t) + ']'


def tlist(entries):
    return '[\n    ' + ',\n    '.join(tmpl(e['template']) for e in entries) + ']'


def tlen(t):
    return sum(2 * len(f) + 1 for f, _ in t)


def lean_family(fam, levels):
    parts, names = [], []
    i = 0
    while i < len(levels):
        lv = levels[i]
        kt = b(lv['orbit'] == 'T')
        name = f'col{fam}{len(names)}'
        names.append(name)
        if lv['kind'] == 'place':
            parts.append(f'def {name} : ColStep := .single {kt} {lv["base"]} {tlist(lv["entries"])}\n')
            i += 1
        else:
            nxt = levels[i + 1]
            assert nxt['orbit'] == lv['orbit'] and nxt['kind'] != 'place'
            parts.append(f'def {name} : ColStep := .final {kt} {tlist(lv["entries"])} {tlist(nxt["entries"])}\n')
            i += 2
    return parts, names


def write_lean():
    with open(DST) as fh:
        data = json.load(fh)
    parts = [HEADER]
    fams = data['families']
    names = {}
    for fam in 'OE':
        p, names[fam] = lean_family(fam, fams[fam]['time_order_levels'])
        parts += p
    L = max(tlen(e['template']) for fam in 'OE' for lv in fams[fam]['time_order_levels'] for e in lv['entries'])
    keys = {fam: [(len(l['entries']), l['w']) for l in fams[fam]['time_order_levels']] for fam in 'OE'}
    assert keys['O'] == keys['E'], 'the families must have the same keys'
    parts.append('/-- **The colour lists.** -/\ndef colourData : ColourData where\n'
                 f'  stepsO := [{", ".join(names["O"])}]\n  stepsE := [{", ".join(names["E"])}]\n  L := {L}\n')
    parts.append('end RubiksGN\n')
    with open(OUT, 'w') as fh:
        fh.write('\n'.join(parts))
    print('wrote', os.path.normpath(OUT), 'L', L, 'keys', keys['O'])
    write_check(names)


CHECK_HEADER = """import RubiksGN.ColourData

/-!
# The kernel check of the colour lists

Generated by `scripts/gen_col.py`. Do not edit. `ColourData.check` for `colourData`, one step per declaration, because the kernel's
caches are freed between declarations: one `decide +kernel` on the whole check peaks at 24 GB. `plcO k`, `plcE k` are the placed
positions before step `k` of a family.
-/

namespace RubiksGN

theorem famCheck_step {d : Bool} {st : ColStep} {t : List ColStep} {p : Placed} (h₁ : st.check d p = true)
    (h₂ : famCheck d t (st.next p) = true) : famCheck d (st :: t) p = true := by
  simp only [famCheck, h₁, h₂, Bool.and_self]
"""

CHECK_FOOTER = """/-- **The check of the colour lists.** -/
theorem colourData_check : colourData.check = true := by
  have hk : (colourData.lvE.map CLevel.key == colourData.keys) = true := by decide +kernel
  have hO : levelsCheck colourData.L colourData.lvO = true := by decide +kernel
  have hE : levelsCheck colourData.L colourData.lvE = true := by decide +kernel
  have h1 : famCheck true colourData.stepsO ([], []) = true := famO_ok
  have h2 : famCheck false colourData.stepsE ([], []) = true := famE_ok
  simp only [ColourData.check, h1, h2, hk, hO, hE, Bool.and_self]

end RubiksGN
"""


def write_check(names):
    parts = [CHECK_HEADER]
    for fam, d in (('O', 'true'), ('E', 'false')):
        ns = names[fam]
        for k, nm in enumerate(ns):
            prev = '([], [])' if k == 0 else f'plc{fam}{k - 1}'
            parts.append(f'def plc{fam}{k} : Placed := ' + ('([], [])' if k == 0 else f'{ns[k - 1]}.next {prev}') + '\n')
            parts.append(f'theorem col{fam}_ok{k} : {nm}.check {d} plc{fam}{k} = true := by decide +kernel\n')
        last = f'{ns[-1]}.next plc{fam}{len(ns) - 1}'
        parts.append(f'theorem col{fam}_end : famCheck {d} [] ({last}) = true := by decide +kernel\n')
        proof = f'col{fam}_end'
        for k in reversed(range(len(ns))):
            proof = f'famCheck_step col{fam}_ok{k} ({proof})'
        parts.append(f'theorem fam{fam}_ok : famCheck {d} [{", ".join(ns)}] ([], []) = true :=\n  {proof}\n')
    parts.append(CHECK_FOOTER)
    with open(OUT_CHECK, 'w') as fh:
        fh.write('\n'.join(parts))
    print('wrote', os.path.normpath(OUT_CHECK))


if __name__ == '__main__':
    if '--rebuild' in sys.argv or not os.path.exists(DST):
        build_json()
    write_lean()
