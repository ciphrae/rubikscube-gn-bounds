import RubiksGN.SolveColoured
import RubiksGN.ColouredLimit

/-!
# God's number of the coloured cube, for valid colour lists

With `Λ = Σ log₂ (m / w)` over the levels of valid data `D`, God's number of the coloured cube is at most
`(Λ / 8 + ε) n² / log₂ n` for all large `n`.
-/

namespace RubiksGN

/-- **The upper bound for the coloured cube, for valid colour lists.** -/
theorem godColoured_limit (μ : Metric) (D : ColourData) (hD : D.Valid) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (godColoured μ n : ℝ) ≤
      (sumRatio D.keys / 8 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨N, hN⟩ := colouredW_limit D.keys hD.keys_lt D.L ε hε
  refine ⟨max N 3, fun n hn => ?_⟩
  obtain ⟨S, Cslot, sOf, Tb, hS0, hS, hp, hW⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hle := godColoured_le_colouredW μ (le_trans (le_max_right _ _) hn) D hD S Cslot sOf Tb hS0 hS hp
  exact le_trans (by exact_mod_cast hle) hW

end RubiksGN
