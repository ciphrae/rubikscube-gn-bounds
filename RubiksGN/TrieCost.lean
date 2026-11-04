import Mathlib

/-!
# The word length of the round scheme with trie slots

A pass over a chunk of `s` rows, with values in a list of `m` templates of total length `w`, costs at most
`|Y| + 2 w (1 + m + ⋯ + m^(s-1))` (`RubiksGN/Trie.lean`), against `|Y| + m^s · 2 s L` for `passW`. A list is keyed by `k = (m, w)`,
and `sOf k` is its chunk size. So the number of rounds and the slots add up over the lists:
with `r = n/2 - 1`,

`trieExactW = 3n + 406 + 2200 r (S + 2) + R r²/S + 2 (r/S + 1) Σ_k (S/2/s_k + 1) 2 w_k (1 + m_k + ⋯ + m_k^(s_k - 1))`.
-/

namespace RubiksGN

/-- `1 + m + ⋯ + m^(s-1)`. -/
def geomS (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => 1 + m * geomS m s

theorem geomS_mono {m : ℕ} (hm : 1 ≤ m) {a b : ℕ} (h : a ≤ b) : geomS m a ≤ geomS m b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [geomS]
    rename_i k _
    have : geomS m k ≤ m * geomS m k := Nat.le_mul_of_pos_left _ hm
    omega

/-- `(m - 1) (1 + m + ⋯ + m^(s-1)) + 1 = m^s`. -/
theorem geomS_mul (m s : ℕ) (hm : 1 ≤ m) : (m - 1) * geomS m s + 1 = m ^ s := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  induction s with
  | zero => simp [geomS]
  | succ s ih =>
    simp only [geomS, Nat.add_sub_cancel] at ih ⊢
    rw [pow_succ, ← ih]
    ring

/-- The number of rounds of a program on a block of at most `S` rows. -/
def trieRounds (S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) : ℕ :=
  (ks.map fun k => S / 2 / sOf k + 1).sum

/-- The edges of one half of a block: one list after the other. -/
def trieSlots (S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) : ℕ :=
  (ks.map fun k => (S / 2 / sOf k + 1) * (2 * k.2 * geomS k.1 (sOf k))).sum

/-- **The total number of quarter turns of the round scheme with trie slots.** -/
def trieExactW (n S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) : ℕ :=
  3 * n + 406 + 2200 * ((n / 2 - 1) * (S + 2)) + trieRounds S sOf ks * ((n / 2 - 1) ^ 2 / S) +
    2 * ((n / 2 - 1) / S + 1) * trieSlots S sOf ks

end RubiksGN
