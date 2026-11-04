#!/usr/bin/env python3
"""Independent verifier for scripts/chain_col.json. Exit status 0 iff every check passes.

It shares no code with chain_col.py: the only import from the repo is rot.py, the rotation model shared with the
Lean development. Everything else (stickers, slices, faces, covering, templates) is recomputed here.

Conventions (repo coordinates): k in Fin 24 stands for the sticker act k (-u, v, n), a 4-cycle [a,b,c,d] sends the
sticker at position a to position b, and so on. A word is applied left to right. The mirror orbit, in common
coordinates, is k -> act k (-u, -v, n).
"""
import itertools, json, math, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rot import ORDER, act, MUL, INV, RX, RY, RZ

FAILS = []
def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("FAIL:", msg)

N0, U0, V0 = 100, 37, 59
CLAMP = lambda t: N0 - 1 if t == N0 else (-(N0 - 1) if t == -N0 else t)
AX = {'x': 0, 'y': 1, 'z': 2}
ROT = {'x': RX, 'y': RY, 'z': RZ}
def sticker_face(v):
    x, y, z = v
    return 0 if z == N0 else 1 if z == -N0 else 2 if y == N0 else 3 if y == -N0 else 4 if x == N0 else 5
def slice_perm(ax, layer, d, base):
    """perm of Fin 24 (list p: position k goes to p[k]) induced by turning `layer` of `ax` on the orbit of base"""
    r = ROT[ax] if d == 1 else INV[ROT[ax]]
    return [MUL[r][k] if CLAMP(act(k, base)[AX[ax]]) == layer else k for k in range(24)]
T_BASE = (-U0, V0, N0)
M_BASE = (-U0, -V0, N0)
ID = list(range(24))
def compose(a, b):  # a after b
    return [a[b[i]] for i in range(24)]
def inverse(a):
    r = [0] * 24
    for i, x in enumerate(a):
        r[x] = i
    return r
def from_cycle(c):
    p = list(range(24))
    for i in range(4):
        p[c[i]] = c[(i + 1) % 4]
    return p

def face_sets():
    kc = [sticker_face(act(k, T_BASE)) for k in range(24)]
    kcm = [sticker_face(act(k, M_BASE)) for k in range(24)]
    check(kc == kcm, "mirror common coordinates must preserve the face of a sticker")
    return kc, [[k for k in range(24) if kc[k] == c] for c in range(6)]

def word_action(word, frame_base):
    """Permutation of a list of pieces [[faceword],ax,sign,dir]; faceword=[[ax,sign,dir],...]; piece = f, r, f^-1."""
    P = ID
    for (fw, ax, sgn, di) in word:
        for (fa, fs, fd) in fw:
            check(abs(fs) == 1, "face move sign")
            P = compose(slice_perm(fa, fs * (N0 - 1), fd, frame_base), P)
        P = compose(slice_perm(ax, sgn * U0, di, frame_base), P)
        for (fa, fs, fd) in reversed(fw):
            P = compose(slice_perm(fa, fs * (N0 - 1), -fd, frame_base), P)
    return P

def move_count(word):
    return sum(1 + 2 * len(fw) for (fw, ax, sgn, di) in word)

def check_scheme(name, scheme, faces, kc, K, L, stats):
    total_log = 0.0
    stages = scheme["stages"]
    check(len(stages) == 5, name + ": five stages")
    placed = []
    z = 1
    maxlen = 0
    for j, st in enumerate(stages):
        col = st["colour"]
        F = sorted(faces[col])
        omega = sorted(k for k in range(24) if k not in placed)
        check(sorted(st["omega"]) == omega, f"{name} stage {j}: omega")
        N = len(omega)
        for li, d in (("list1", 1), ("list2", -1)):
            for e in st[li]:
                c = e["c"]
                check(len(set(c)) == 4 and set(c) <= set(omega), f"{name} stage {j} {li}: support in omega {c}")
                D = e["D"]
                y = e["y"]
                check(sorted(D) == sorted(faces[y]), f"{name} stage {j}: D is a 4-cycle on one whole face")
                check(not set(D) & set(c), f"{name} stage {j}: c and D disjoint")
                if "word" in e:
                    P = word_action(e["word"], T_BASE)
                    Pm = word_action(e["word"], M_BASE)
                    check(P == Pm, f"{name} stage {j}: row word acts diagonally on target and mirror")
                    Kd = K if d == 1 else inverse(K)
                    Ld = L if d == 1 else inverse(L)
                    check(compose(inverse(P), compose(Kd, P)) == from_cycle(c), f"{name} stage {j}: word realises c {c}")
                    check(compose(inverse(P), compose(Ld, P)) == from_cycle(D), f"{name} stage {j}: word realises D {D}")
                    maxlen = max(maxlen, move_count(e["word"]))
        m1, m2 = len(st["list1"]), len(st["list2"])
        total_log += math.log2(m1) + math.log2(m2)
        # exhaustive covering, using the witness table only as a hint
        wit = {tuple(w[0]): (w[1], w[2]) for w in st["witness"]}
        count = 0
        for A in itertools.combinations(omega, 4):
            count += 1
            if A not in wit:
                check(False, f"{name} stage {j}: no witness for {A}")
                continue
            i1, i2 = wit[A]
            p1 = from_cycle(st["list1"][i1]["c"])
            p2 = from_cycle(st["list2"][i2]["c"])
            check(sorted(p2[p1[a]] for a in A) == F, f"{name} stage {j}: witness fails on {A}")
        check(count == math.comb(N, 4), f"{name} stage {j}: count")
        z *= count
        placed += F
    check(z == math.factorial(24) // 24 ** 6, name + ": product of the stage counts is Z")
    stats[name] = (total_log, maxlen)
    return total_log

def random_end_to_end(scheme, faces, kc, trials=2000):
    """Abstract run: random labelled state, chain chosen by witness on the current state. Final state must lie in Y."""
    rng = random.Random(1)
    for _ in range(trials):
        sigma = list(range(24)); rng.shuffle(sigma)     # sigma[label]=position
        mirror = [x for x in ID]                         # an already solved mirror orbit
        for st in scheme["stages"]:
            wit = {tuple(w[0]): (w[1], w[2]) for w in st["witness"]}
            A = tuple(sorted(sigma[k] for k in faces[st["colour"]]))
            i1, i2 = wit[A]
            for li, i in (("list1", i1), ("list2", i2)):
                c = from_cycle(st[li][i]["c"]); D = from_cycle(st[li][i]["D"])
                sigma = [c[x] for x in sigma]
                mirror = [D[x] for x in mirror]
        check(all(kc[sigma[k]] == kc[k] for k in range(24)), "end to end: target not in Y")
        check(all(kc[mirror[k]] == kc[k] for k in range(24)), "end to end: solved mirror left Y")

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), "chain_col.json")
    data = json.load(open(path))
    kc, faces = face_sets()
    check([sorted(f) for f in data["faces"]] == faces, "faces in the JSON equal the kc fibres")
    check(all(len(f) == 4 for f in faces), "each face has four coordinates")
    K = slice_perm('x', V0, 1, T_BASE)
    L = slice_perm('x', -V0, 1, T_BASE)
    check(L == slice_perm('x', V0, 1, M_BASE), "L is the action of the same column on the mirror frame")
    check(sum(K[i] != i and L[i] != i for i in range(24)) == 0, "K and L disjoint")
    check(data["K"][:2] == [data["K"][0], K[data["K"][0]]], "K cycle agrees")
    # row group: <pieces> = S_24 (needs sympy, part of pyproject)
    try:
        from sympy.combinatorics import Permutation, PermutationGroup
        fm = [('z', 1), ('z', -1), ('y', 1), ('y', -1), ('x', 1), ('x', -1)]
        fp = [slice_perm(a, s * (N0 - 1), 1, T_BASE) for a, s in fm]
        rp = [slice_perm(a, s * U0, 1, T_BASE) for a in 'xyz' for s in (1, -1)]
        g = PermutationGroup([Permutation(p) for p in fp + rp])
        n = PermutationGroup([Permutation(p) for p in rp]).normal_closure(g)
        check(n.order() == math.factorial(24), "the pieces f r f^-1 generate S_24")
    except ImportError:
        check(False, "sympy is needed")
    stats = {}
    for name in data["schemes"]:
        scheme = data["schemes"][name]
        B = check_scheme(name, scheme, faces, kc, K, L, stats)
        check(abs(B - scheme["B_sum_logs"]) < 1e-9, name + ": recorded sum of logs")
        random_end_to_end(scheme, faces, kc)
    if FAILS:
        print(len(FAILS), "failures")
        sys.exit(1)
    for name, (b, ml) in stats.items():
        pairs = [(len(s["list1"]), len(s["list2"])) for s in data["schemes"][name]["stages"]]
        eq = sum(2 * math.log2(max(p)) for p in pairs)
        print(f"{name}: sizes {pairs}  B_sum_logs={b:.4f} (limit {b/4:.4f})  B_same_block=2 log2 max={eq:.4f} (limit {eq/4:.4f})  longest word {ml} moves")
    print(f"log2 Z = {math.log2(math.factorial(24)/24**6):.4f}, limit floor {math.log2(math.factorial(24)/24**6)/4:.4f}")
    print("OK")

if __name__ == "__main__":
    main()
