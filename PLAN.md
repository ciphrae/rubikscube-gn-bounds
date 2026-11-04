# PLAN: closing the gap on God's number of the n×n×n cube

**Status: done for the leading constants.** `main_limits` in `RubiksGN/MainAll.lean` proves both limits. The section on frozen D below is historical: rounds replaced it. Open items are listed in README.md.

Knowledge transfer between sessions. Read `README.md` first for the current proved results.

Limits before this work, per `n²/log₂ n`: lower 12.88 (coloured, all metrics), upper 137.5 (labelled, qtm).

## Information-theoretic targets (now proved)

- Labelled cube: limit `log₂(24!/2)/4` = 19.509.
- Coloured cube: limit `log₂(24!/(4!)⁶)/4` = 12.882.

## Historical: the first scheme, "one column move carries log₂ n bits"

Old scheme: a universal sequence of 275 binary letters (3-cycles), each letter a Lupanov cover costing
`2 |R||C| / s`. Two sources of waste:
1. 275 binary letters for 78 bits of entropy: factor 3.5.
2. A column turned at one slot and turned back at one slot uses two moves to carry `log₂ T` bits: factor 2.

New scheme. Fix a block `X` of `s` rows and a column set `Y` with no index in common with `X` (index of a
layer = |coordinate|). A *value* is a row configuration `h` (a word in face turns and slices of the row's own
index whose face part cancels). A *pass* is a list of slots, one for each pattern `p : X → Values` used by some
column:

```
slot(p) = G(p) · [turn every column j whose pattern is p, direction d] · G(p)⁻¹
G(p)    = concatenation over i ∈ X of the template of value p(i), played on row i only
```

So one pass moves each column once, at the slot of its own pattern. On the orbit (i, j), i ∈ X, j ∈ Y, the pass
acts by `c = h_{p_j(i)} κ^d h_{p_j(i)}⁻¹`, a 4-cycle chosen freely from a list, because the configuration is undone
in every slot. Every column move has its own free pattern, so one column move carries `log₂ T` bits, where
`T ≈ n/polylog n` is the number of slots, against `½ log₂ T` per move before.

Two passes with opposite direction form a *pair phase*: `(i, j) ↦ c₁ c₂`, and orbits not meeting `X` see `κ κ⁻¹ = 1`.

Cost of a pair phase on one block: `2|Y| + (T₁ + T₂)·2·s·L`, `L` = longest template. With `r/s` blocks and
`m^s = T`: a pair with lists of size `m` costs `(r/s)·2c = 2 r c log₂ m / log₂ T`, so **cost = (n²/4) · B / log₂ n**
where `B = Σ_pairs 2 log₂ m_k`, summed over all pair phases. Limit constant = `B/4`.

### Factorization requirement

Lists `T₁, T₂, …, T_{2K}` of 4-cycles of Fin 24 with `T₁ T₂ ⋯ T_{2K} ⊇ A₂₄`. A stabilizer chain with 1 point
per list is exact: `T_k` = one 4-cycle for each image of the base point `b_k` (`|T_k| = |Ω_k|`, the unplaced points),
for example `(b_k a x y)` for image `a ≠ b_k` and any 4-cycle missing `b_k` for image `b_k`. So `B ≈ log₂ 24! ≈ 79`, and the
limit constant is about **20**, vs 19.51 lower bound. Old 3-cycle chains could not do this: a 3-cycle with binary
choice extends a point's reachable set by one per letter (275 letters), whereas here a single toggle has `|Ω|` values.

### The obstruction: mirror orbits are locked (found by computation, `scripts/orbit_model.py`)

The slices of one index `u` plus the faces act **diagonally** on the two orbits `rep(u,v)` and `rep(v,u)`: the map
`φ` flipping the sign of the coordinate of absolute value `v` is an equivariant bijection between them. The group
they generate on the 48 points has order `24!`, not `(24!)²/2`. So a row configuration cannot be trivial on the
mirror orbit and nontrivial on the target. Consequently, in common coordinates (mirror pulled back by φ), a toggle of column
`x=+v` at configuration `h` acts by

```
target copy: h K h⁻¹        mirror copy: h L h⁻¹
K = x=+v on rep(u,v) = (5 13 21 19), L = x=−v on rep(u,v) = (3 9 18 8)      (disjoint, in repo coordinates)
```

**Fix (frozen D).** In a pair phase require `h L^d h⁻¹ = D` for all values of the first pass, and `h L^{-d} h⁻¹ = D⁻¹`
for all values of the second pass, for one fixed 4-cycle `D`. Then the mirror copy nets to 1, and the target gets
`c₁ c₂` with `c₁, c₂` 4-cycles disjoint from `D`. So: **all 4-cycles of one pair phase avoid a frozen 4-set**. Once four points
are placed, take `D` on those points: the chain is unconstrained and exact. The first two pair phases have to avoid
`D` before anything is placed, which wastes about 2 bits each with tags (see below). Estimated `B ≈ 83`, limit ≈ 20.8.

Tags: `D` may depend on the value as long as the two chosen values share `D`. So a value is (image, tag), with tag sets
forming an intersecting family: each image gets 2 of 3 tags with `D_A, D_B, D_C` disjoint, giving lists of 48 for placing the first two points.

### Index collisions

Columns with an index in `X` must not be toggled in `X`'s pass (they would be conjugated by row configurations and
hit every orbit of that row). So `Y = C \ idx(X)`, also excluding the outer column and the middle column. The excluded orbits number
`O(r·s)` per pair phase plus `2r`, and are finished by the old rectangle gadget on singletons: 275 letters × 8 moves each.
Lower order.

### Classification of orbits under a pair phase, with `u = |row coord|`, `v = col coord`, for `rep i j`

- `u ∈ X, v ∈ Y`: target, `c₁c₂`.
- `v ∈ X, u ∈ Y`: mirror, net 1 by frozen `D`.
- `u ∈ X` or `v ∈ X`, otherwise: no toggled column touches the orbit, each slot is `G·G⁻¹ = 1`.
- `u, v ∉ X`: `G` acts by its face part, which cancels, so the slots are plain column turns, and they cancel over the two passes.

### Templates

Row group: all six slices of index `u` (x, y, z, ±u) plus faces. `x` slices alone do not suffice: they never touch
the left and right faces' stickers of the orbit, and generate only a group of order `16!·16`. Templates are lists of pieces
`f r f⁻¹` where `f` is a word of face turns and `r` is one slice of index `u`, so the face part cancels by construction.

## Exact scheme ("rounds"): supersedes frozen D and pair phases, target limit = lower bound exactly

Goal: `godLabelled μ n ~ (log₂(24!/2)/4) · n²/log₂ n` (19.509), proved in Lean.
Everything below was derived after the first agent round; `RubiksGN/Pass.lean` is the base (passW, pass_target, pass_mirror,
pass_plain, pass_trivial). Pair phases and frozen `D` are NOT needed any more.

**Rounds.** Round = `passW XO Y τ₁ pat₁ true ++ passW XE Y τ₂ pat₂ false`, with `XO, XE ⊆ Q` disjoint. A row not in the pass's `X` sees
the plain column turn. So on `rep i j` (`i ∈ Q`, `j ∈ Y`), one round acts by
- `i ∈ XO`: `conjT τ₁ true * colK⁻¹`, `i ∈ XE`: `colK * conjT τ₂ false`, otherwise `colK * colK⁻¹ = 1`;
and on the mirror orbit `rep i j` (`rev j ∈ Q`, `rev i ∈ Y`) likewise with `conjM`, `colM`.
All other orbits see 1. So a row informative in a pass spends one column move per column on one list, and every pass is fully used
by the rows of that pass only: there is no list-size mismatch, and the bits per column move are `log₂ T` for any list size.

Elements: `eT τ = conjT τ true * colK⁻¹`, `eM τ = conjM τ true * colM⁻¹` (commutators `[h, K]`, `[h', K']`). `XE` rows get `eT⁻¹`.

**Program for a coarse block `Q` of rows, `Y` = columns of later blocks.** `Q = Q_O ⊔ Q_E` of size ≤ S/2 each. `Q_O` rows run lists
`1..N`, `Q_E` rows run lists `N..1` (so they act by the inverse of the product), each list cut into chunks of size `s_k` (`m_k^{s_k} ≈ T`).
Rounds zip the two job lists. Each unordered index pair `{a,b}` in different coarse blocks is handled once, by the earlier block, and
both of its orbits are solved at once: target `rep(a, b)` and mirror `rep(b, a)`. No ordering issue: every other program acts by 1 on them.
Same-block orbits and the outer/middle columns are finished by the old gadget (`2200` moves per orbit).

**Universal lists (kernel-checked data).** `ls : List (List Tmpl)` with: for all even `π₁ π₂` there is a choice of one template per list with
`∏ eT = π₁` and `∏ eM = π₂`. Exact design, 42 lists, `∏ m_k = (24!/2)²`, so `Σ log₂ m_k = 2 log₂(24!/2)`:
- Target chain: base points avoid supp K until 5 points remain; list sizes 24, 23, …, 6, then exact A₅ = X·Y with |X| = 5, |Y| = 12 (exists,
  found by search, elements `cK⁻¹` on 5 points containing supp K). Mirror chain: identical sizes.
- In common coordinates (φ) `h` gives any disjoint pair `(c, D) = (hKh⁻¹, hLh⁻¹)`. Let `Ω_f ⊇ supp K`, `Ω'_f ⊇ supp L` be disjoint 5-sets. Target places
  `Ω'_f` first, mirror places `Ω_f` first, in interleaved order `T₁,M₁,…,T₅,M₅`. Then all later target levels can take `D = L` (mirror element 1) and
  all later mirror levels `c = K`. In the first 10 levels the other element is garbage, which only has to fix what is placed.

**Cost.** See `RubiksGN/ExactCost.lean`: `exactW`. Limit: `(n²/8)·Σ log₂ m_k / log₂ n`, that is `(log₂(24!/2)/4) n²/log₂ n`.

Coloured cube: same rounds with colour-level lists and the covering lemma; see README.md, step 5.

## Status and how to continue

- Proved in Lean: both limits, closed second-order forms, explicit `(N₀, C)` tables. Comparator accepts. See README.md.
- Bug to remember: `scripts/constants_exact.py` first searched block sizes only up to `lg n / 2` for the old formula; fixed.
- Ideas not pursued:
  - Row moves carrying information could remove the `lg lg n` term in the upper bound. A clean model: is every boolean `r × c` matrix an XOR of about
    `rc / ((r+c)(lg n − O(1)))` Ferrers matrices? (Each Ferrers matrix is one shuffle of row moves and column moves.)
  - Move-level trie (`c ≈ 7.1`), mixed-radix chunks (`c ≈ 6.3`, estimate); replacing the 2200 by about 700 (estimate) only matters near `n ≈ 10³`.
  - Wide-move metric: limit is between half and all of these constants. Laminar intervals telescope but carry only about 2 bits per endpoint; a new idea is needed.
