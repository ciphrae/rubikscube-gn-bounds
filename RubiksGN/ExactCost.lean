import Mathlib

/-!
# The word length of the round scheme

`ms` are the list sizes, `S` the coarse block size (even), `sOf m` the chunk size for a list of size `m`, and `Cslot` a bound on the
slots of one pass: `m ^ sOf m * (2 * sOf m * L) ≤ Cslot`. With `r = n/2 - 1` rows:

`3n + 406`: parity repair and skeleton. `2200 r (S + 2)`: old gadget on the same-block orbits and the outer and middle columns.
`R (r²/S + 2 (r/S + 1) Cslot)`: the programs, where `R` is the number of rounds of a program.
-/

namespace RubiksGN

/-- The number of rounds of a program on a block of at most `S` rows. -/
def exactRounds (S : ℕ) (sOf : ℕ → ℕ) (ms : List ℕ) : ℕ :=
  (ms.map fun m => S / 2 / sOf m + 1).sum

/-- The total number of quarter turns of the round scheme. -/
def exactW (n S Cslot : ℕ) (sOf : ℕ → ℕ) (ms : List ℕ) : ℕ :=
  3 * n + 406 + 2200 * ((n / 2 - 1) * (S + 2)) +
    exactRounds S sOf ms * ((n / 2 - 1) ^ 2 / S + 2 * ((n / 2 - 1) / S + 1) * Cslot)

end RubiksGN
