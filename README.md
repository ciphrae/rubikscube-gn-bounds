# rubikscube_gn_bounds

A Lean 4 / Mathlib proof of the exact leading constant of God's number of the `n × n × n` Rubik's cube.
Demaine, Demaine, Eisenstat, Lubiw and Winslow (*Algorithms for Solving Rubik's Cubes*, 2011) proved `Θ(n² / log n)`.
This repository proves, with `log₂` the base-2 logarithm and in both metrics:

```text
god(n) · log₂ n / n²  →  log₂(24!/(4!)⁶) / 4 ≈ 12.882       (the real, coloured cube)
diam(n) · log₂ n / n²  →  log₂(24!/2) / 4    ≈ 19.509       (the diameter of the cube group)
```

So the counting lower bound is asymptotically tight (`main_limits`). The first limit is the constant Ben Whitmore conjectured in the
[OEIS entry A257401](https://oeis.org/A257401) (2021). That page is about the half-turn metric but does not define moves
for large cubes; here a move is a turn of one layer, inner layers included (see [What exactly is proved](#what-exactly-is-proved)).
A web search during this work found no earlier proof, and that search was not exhaustive.

No `sorry`, no `native_decide`; the only axioms are `propext`, `Classical.choice` and `Quot.sound` (`Checks/Audit.lean`).
Comparator accepts the statements (`Checks/comparator.sh`).

## Results

Per `n²/log₂ n`; multiply by `ln 2 ≈ 0.693` to get a constant per `n²/ln n`.

| | limit | theorem |
|---|---:|---|
| labelled cube (`godLabelled`), lower and upper | `log₂(24!/2)/4`, between 19.509 and 19.51 | `main_limits`, `lgE_bounds` |
| coloured cube (`godColoured`), lower and upper | `log₂(24!/24⁶)/4`, between 12.88 and 12.8821 | `main_limits`, `lgZ_div_four`, `logZ_div_four_le` |

The older bounds in this repository had limits 12.88 (lower) and 137.5 (upper) for all four versions, a factor of 10.7.

### Explicit lower-order terms

For `n ≥ 2⁶⁴` and both metrics, with no `ε`, and with the exact main terms `E = log₂(24!/2)/4` and `Ez = log₂(24!/(4!)⁶)/4`
on both sides (`main_labelled_exact`, `main_coloured_exact`):

```text
(E (n+1)(n−3) − 1) / (log₂ n + 2.89)       ≤  godLabelled  ≤  E n² / (log₂ n − log₂log₂ n − 7.59)
(Ez (n−1)(n−3) − 16.6) / (log₂ n + 2.89)   ≤  godColoured  ≤  Ez n² / (log₂ n − 3 log₂log₂ n − 7.63)
```

So the bounds differ only in lower-order terms: by the factor `(log₂ n + 2.89) / (log₂ n − log₂log₂ n − 7.59)` for the labelled cube, plus `O(1/n)`.
The lower bounds hold for all `n ≥ 3`, and the `2.89` improves to `2.33` in the quarter-turn metric (`lowerExact_labelled`, `lowerExact_coloured`,
with `dMove μ`). They count words up to the commutation of parallel moves. Versions with the decimals `19.509 ≤ E ≤ 19.51` and
`12.88 ≤ Ez ≤ 12.8821` are `main_labelled_second_order`, `main_coloured_second_order`, `main_lower_htm` and `main_lower_qtm`. The remaining gap is in the
denominators: see [Open](#open).

### Explicit constants

`C` such that the bound is `C n² / log₂ n` for all `n ≥ N₀` (`explicit_100`, `main_explicit'`, `explicit_128`, `explicit_256`, `explicit_1024`, `coloured_explicit`). The coloured upper column is `coloured_explicit` from `2⁶⁴` on; below that it is the labelled bound. The lower columns
evaluate the closed forms above at `n = N₀` in `htm`, rounded down; they are not separate theorems.

| `N₀` | labelled lower | labelled upper | coloured lower | coloured upper |
|---:|---:|---:|---:|---:|
| 100 | 13.3 | 567 | 8.6 | 567 |
| 2¹⁶ | 16.5 | 61 | 10.9 | 61 |
| 2³² | 17.8 | 31 | 11.8 | 31 |
| 2⁶⁴ | 18.6 | 24.8 | 12.3 | 21.49 |
| 2¹²⁸ | 19.0 | 22.1 | 12.5 | 16.6 |
| 2²⁵⁶ | 19.2 | 20.8 | 12.7 | 14.7 |
| 2¹⁰²⁴ | 19.4 | 19.9 | 12.8 | 13.38 |

The older bound `C = 1800` for all `n ≥ 3` (`main_upper_all`, for the coloured cube; `upper_explicit` for the labelled one) is still the only one below `n = 100`.

### Evaluating the exact formulas

The closed forms above lose some precision. `scripts/constants_exact.py` evaluates the exact proved word lengths with good parameters from a coarse search, so the numbers are slightly conservative. Upper bound per `n²/log₂ n`, for the
labelled cube:

| `n` | old scheme | new scheme | upper / lower |
|---:|---:|---:|---:|
| 100 | 560 | 755 | 42 (old) |
| 1 000 | 397 | 189 | 12.5 |
| 10⁶ | 255 | 43.0 | 2.52 |
| 10⁹ | 215 | 31.1 | 1.75 |
| 10¹² | 195 | 27.5 | 1.51 |
| 2⁶⁴ | 174 | 24.2 | 1.30 |
| 2¹⁰⁰ | 162 | 22.5 | 1.19 |
| 2¹⁰⁰⁰ | 141 | 19.8 | 1.02 |

The new scheme wins from about `n = 183`. The formula behind the new column is `godLabelled_le_trie`.

## What exactly is proved

A sticker is an integer vector on the surface of `[-n, n]³`; a move turns one of the `n` layers of one of
the three axes, so there are `9n` moves (`RubiksGN/Basic.lean`). Four versions of God's number are
defined:

| | half turn counts as one move (`htm`) | quarter turns only (`qtm`) |
|---|---|---|
| real cube: positions are colourings, solved = monochromatic faces (`godColoured`) | smallest | |
| labelled stickers, solved = identity; the diameter of the group (`godLabelled`) | | largest |

All four are covered. Turning several adjacent layers as one "wide" move is not a single move in this model.

The model was checked independently: `scripts/validate_model.py` computes group orders from the same
formulas with sympy and recovers 88 179 840 for `n = 2`, 43 252 003 274 489 856 000 × 24 for `n = 3`,
and the known 7.401·10⁴⁵ for `n = 4`.

## Proof outline

Each of the `≈ n²/4` inner orbits has 24 stickers. An orbit has coordinates `Fin 24`, indexed by a row `u` and a column `v` (indices are
absolute layer coordinates).

**Lower bound.** On each orbit every even permutation is reachable independently, so there are `(24!/2)^(n²/4)` group elements, or `Z^(n²/4)`
coloured positions with `Z = 24!/(4!)⁶`. Words of length `k` give at most `2 (c n)^k` permutations, with `c = 7.4` in `htm` and `c = 5` in `qtm` (`LowerCommute`).

**Upper bound.** The classical approach turns each bit of each orbit into a commutator; two sources of waste made it lose a factor 7.
The new scheme uses all of the `log₂ n` bits of each column move.

1. *Pass.* Fix a block `X` of rows and a set `Y` of columns. One slot per pattern `p : X → values`:
   `G(p) · [turn the columns of pattern p] · G(p)⁻¹`, where `G(p)` puts each row into a configuration `h` given by a template, a word of face
   turns and slices of the row's own index whose face part cancels. The orbit `(i, j)` receives `h K h⁻¹`, a 4-cycle chosen from a whole list, and all else cancels (`Pass`).
   So each column move carries `log₂(number of slots) ≈ log₂ n` bits.
2. *Rounds.* A column turned in a pass for a chunk of rows is turned back in the next pass, for another chunk. A row outside the pass sees
   the plain turn `K`, so a row in the chunk receives the commutator `h K h⁻¹ K⁻¹` and every other row receives 1 (`Rounds`). Each pass serves its own chunk with its own list size, so nothing is
   wasted when list sizes differ.
3. *Mirror orbits.* Slices of one index and faces act diagonally on the orbits `(u,v)` and `(v,u)`: a computation shows the group on the 48 points has order `24!`.
   So they can't be treated separately. Instead, each unordered pair is handled once, and one row configuration acts on both orbits by `(h K h⁻¹ K⁻¹, h L h⁻¹ L⁻¹)`
   with `K, L` disjoint. Programs on one coarse block of rows use the columns of later blocks only (`Program`, `SolveExact`).
4. *Exact factorization.* 42 lists of templates, with sizes multiplying to exactly `(24!/2)²`, such that every pair of even permutations is a product (`ExactData`, `ExactChain`):
   a stabilizer chain of sizes 24, 23, …, 6 for each orbit, and an exact factorization of `Alt(5)` of shape 5 × 12 at the end. Ordering the levels makes the two chains
   independent after the first ten levels. Each list of size `m` costs `(n²/8) log₂ m / log₂ n`, so the limit is exactly the counting bound (`ExactLimit`).
5. *Coloured cube.* It suffices to give each position the right colour. In a level placing position `b`, exactly `w = 4 − #(placed positions of its colour)` of the `m` templates are good, whatever the
   state, and `∏ m/w` is exactly `Z²` over both orbits. A greedy covering lemma (`Covering`) gives about `(m/w)^s ln n` patterns of `s` rows that meet the good
   boxes of all columns, so a pass carries `s log₂(m/w) ≈ log₂ n` bits (`ProgramGen`, `ColourChain`, `SolveColoured`, `ColouredLimit`).
6. *Trie slots.* Consecutive slots cancel their common prefix, which removes a factor `s` from the slot cost (`Trie`, `TrieProgram`).
7. *Remainder.* At most `3n` moves make every layer's turn count even, words of 406 moves fix corners, middle edges and face centres (`Solve`, `Skeleton`), and the old
   rectangle gadget solves the few orbits sharing a block, the outer column and the middle column, at 2200 moves each. Wing partners follow by rigidity (`partner_fixed`).

`RubiksGN/Main.lean` still contains the older theorems (`main_explicit`, `main_upper_all`, `main_asymptotic`, `main_second_order`).

## Open

- **Second-order term.** With the same main term `E` on both sides, the denominators are `log₂ n + 2.89` (`2.33`) below and `log₂ n − log₂log₂ n − 7.59` above. Is the true denominator `log₂ n + O(1)`? Numerical experiments on relations (not proved)
  suggest the word count has no `log log` loss. Any scheme with `T` slots spends about `T` row moves carrying few bits, so the `log₂log₂ n` looks inherent to block schemes (a sketch, not proved). Removing it requires row moves that carry
  information themselves.
- **Coloured second order.** Trie slots do not apply to covering sets, hence `3 log₂log₂ n` there. An improvement would need structured covering codes.
- **Small `n`.** The bounds are far apart below `n ≈ 10⁴`, where the slot, column and 2200-gadget terms are all significant.
- **Wide moves.** If any run of adjacent layers can be turned as one move, counting gives half of these limits, and turning single layers gives at most these limits up to a factor of 2 in the quarter-turn count. Neither the model nor the machinery here covers that gap. If only blocks containing an outer face count, the counting constant is unchanged.

## Reproducing

```sh
lake exe cache get
lake build                         # about 10 minutes from scratch; the coloured kernel check is about 3 of them
lake env lean Checks/Audit.lean    # axioms
Checks/comparator.sh               # about 8 minutes; needs comparator, lean4export and landrun, see the script
uv run python scripts/validate_model.py
uv run python scripts/constants_exact.py
```

`Comparator/Challenge.lean` restates the model and the main statements importing only Mathlib, so reviewing
that one file is enough to know what those statements say. It does not restate the exact word-length formulas, such as `godLabelled_le_trie`. Comparator ends with "Your solution is okay!".
`comparator.json` also lists four helper theorems (`act_isSticker`, `act_inv_act`, `act_act_inv`,
`coord_rx`) because proof fields of the definitions use them: their statements are compared, and their
proofs are checked in the solution, rather than comparing tactic-generated proof terms across modules.

Data generators, which only propose data for Lean to check:

- `scripts/exact_chain.py`, `scripts/gen_exact.py`: labelled lists (`ExactData`); independent checker `scripts/check_exact_chain.py`.
- `scripts/chain_col2.py`, `scripts/gen_col.py`: coloured lists (`ColourData`, `ColourCheck`); independent checker `scripts/check_chain_col2.py`.
- `scripts/gen_trie_octaves.py`: the range checks of the explicit bounds.
- `scripts/sim_pass.py`, `uv run --with numpy python scripts/redteam_col.py`: adversarial simulations on real cubes. Not part of the proof.
- `scripts/gen_rot.py`, `scripts/gen_univ.py`, `scripts/chain.py`, `scripts/gen_skel.py`: data of the older parts.
