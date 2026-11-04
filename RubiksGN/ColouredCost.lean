import Mathlib

/-!
# The word length of the coloured round scheme

A level of a chain is keyed by a pair `(m, w)`: its list has `m` entries, of which at least `w` are good
at any state satisfying the invariant. `sOf` gives the chunk size of a key. With `r = n/2 - 1` rows the
cost has the same form as `exactW`, with `Cslot` bounding the slots of one pass.
-/

namespace RubiksGN

/-- The number of rounds of a program on a block of at most `S` rows. -/
def colRounds (S : ℕ) (sOf : ℕ × ℕ → ℕ) (ms : List (ℕ × ℕ)) : ℕ :=
  (ms.map fun k => S / 2 / sOf k + 1).sum

/-- The total number of quarter turns of the coloured round scheme. -/
def colouredW (n S Cslot : ℕ) (sOf : ℕ × ℕ → ℕ) (ms : List (ℕ × ℕ)) : ℕ :=
  3 * n + 406 + 2200 * ((n / 2 - 1) * (S + 2)) +
    colRounds S sOf ms * ((n / 2 - 1) ^ 2 / S + 2 * ((n / 2 - 1) / S + 1) * Cslot)

/-- The requirements on the parameters for a list of keys. -/
structure ParamsOK (n : ℕ) (L Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ) (ms : List (ℕ × ℕ)) : Prop where
  s_pos : ∀ k ∈ ms, 0 < sOf k
  tb : ∀ k ∈ ms, ((k.1 : ℝ) / k.2) ^ sOf k * (Real.log (n : ℝ) + 1) + 1 ≤ Tb k
  slot : ∀ k ∈ ms, Tb k * (2 * sOf k * L) ≤ Cslot

end RubiksGN
