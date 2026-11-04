import RubiksGN.SecondOrder

/-!
# God's number of the `n × n × n` Rubik's cube is `Θ(n² / log n)`

`godColoured μ n` is the true God's number (positions are colourings, solved means monochromatic
faces); `godLabelled μ n` is the diameter of the cube group. `μ` is the half-turn or the quarter-turn
slice metric. Every bound below holds for all four combinations, because the lower bound is proved for
the smallest quantity and the upper bound for the largest.
-/

namespace RubiksGN

/-- **Main theorem**, with explicit constants, for all `n ≥ 100`. -/
theorem main_explicit (μ : Metric) (n : ℕ) (hn : 100 ≤ n) :
    8 * (n : ℝ) ^ 2 / Real.logb 2 n ≤ godColoured μ n ∧
    godColoured μ n ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤ 650 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  ⟨lower_explicit μ hn, godColoured_le_godLabelled μ (by omega), upper_explicit' μ hn⟩

/-- **The upper bound for every `n ≥ 3`.** -/
theorem main_upper_all (μ : Metric) (n : ℕ) (hn : 3 ≤ n) :
    (godColoured μ n : ℝ) ≤ 1800 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  le_trans (by exact_mod_cast godColoured_le_godLabelled μ hn) (upper_explicit μ hn)

/-- `log₂ Z / 4 ≥ 12.88`, where `Z = 24! / (4!)⁶`. -/
theorem lgZ_div_four : (12.88 : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 := by
  have := LZ_lower
  simp only [LZ, lg, Zval] at this
  linarith

/-- **Main theorem**, with the limiting constants. -/
theorem main_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
      (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 - ε) * (n : ℝ) ^ 2 / Real.logb 2 n ≤
        godColoured μ n ∧
      (godLabelled μ n : ℝ) ≤ (275 / 2 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨N₁, h₁⟩ := lower_asymptotic ε hε
  obtain ⟨N₂, h₂⟩ := upper_asymptotic ε hε
  exact ⟨max N₁ N₂, fun n hn μ => ⟨h₁ n (le_trans (le_max_left _ _) hn) μ,
    h₂ n (le_trans (le_max_right _ _) hn) μ⟩⟩

/-- **Main theorem**, with explicit lower-order terms and no `ε`. -/
theorem main_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 15.6) / (Real.logb 2 n + 3.18) ≤ godColoured μ n ∧
    godColoured μ n ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      275 / 2 * (n : ℝ) ^ 2 / (Real.logb 2 n - 2 * Real.logb 2 (Real.logb 2 n) - 4) := by
  have h3 : 100 ≤ 2 ^ 16 := by norm_num
  exact ⟨lower_second_order μ (by omega), godColoured_le_godLabelled μ (by omega),
    upper_second_order μ hn⟩

end RubiksGN
