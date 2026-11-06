import RubiksGN.MainAll

/-!
# Second-order bounds with the exact main term

The same constant on both sides: `E = log₂(24!/2) / 4` for the labelled cube and `Ez = log₂(24!/24⁶) / 4` for
the coloured cube. Only the denominators (and lower-order corrections in the numerators) differ.
-/

namespace RubiksGN

variable {n : ℕ}

/-- **Labelled lower bound with the exact constant**, for every `n ≥ 3`. -/
theorem lowerExact_labelled (μ : Metric) (hn : 3 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) /
      (Real.logb 2 n + dMove μ) ≤ godLabelled μ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc := count_labelled_commute hn μ _ (labelled_spec μ hn)
  have hE : (0 : ℝ) < evenN := by
    have : 0 < evenN := by decide +kernel
    exact_mod_cast this
  have hcn : 0 < cMove μ * n := mul_pos (cMove_pos μ) hn0
  have h2 := lg_mono (by positivity) hc
  rw [lg_pow, lg_mul (by norm_num) (by positivity), lg_pow, lg_two] at h2
  have hG : (0 : ℝ) ≤ godLabelled μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left (lg_cn_le μ hn) hG
  have hin := fullOrbits_lower hn
  have hL : (0 : ℝ) ≤ lg evenN := by linarith [LE_lower, show LE = lg evenN from rfl]
  have h3 : lg evenN / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) ≤ (fullOrbits n : ℝ) * lg evenN := by
    have := mul_le_mul_of_nonneg_left hin hL
    nlinarith
  have hev : ((Nat.factorial 24 / 2 : ℕ) : ℝ) = (evenN : ℝ) := rfl
  rw [hev]
  show (lg evenN / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (lg n + dMove μ) ≤ _
  rw [div_le_iff₀ (by linarith [lg_pos_of hn, dMove_pos μ])]
  nlinarith

/-- **Coloured lower bound with the exact constant**, for every `n ≥ 3`. -/
theorem lowerExact_coloured (μ : Metric) (hn : 3 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) /
      (Real.logb 2 n + dMove μ) ≤ godColoured μ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc := count_coloured_commute hn μ _ (coloured_spec μ hn)
  have hZ : (0 : ℝ) < Zval := by
    rw [Zval_eq]; norm_num
  have hcn : 0 < cMove μ * n := mul_pos (cMove_pos μ) hn0
  have h2 := lg_mono (by positivity) hc
  rw [lg_pow, lg_mul (by positivity) (by positivity), lg_mul (by norm_num) (by positivity),
    lg_pow, lg_pow, lg_two] at h2
  push_cast at h2
  have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left (lg_cn_le μ hn) hG
  have hin := innerOrbits_lower hn
  have hL : (0 : ℝ) ≤ lg Zval := by linarith [LZ_lower, show LZ = lg Zval from rfl]
  have h3 : lg Zval / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) ≤ (innerOrbits n : ℝ) * lg Zval := by
    have := mul_le_mul_of_nonneg_left hin hL
    nlinarith
  have h6 := lg6_upper
  have hz : ((Nat.factorial 24 / 24 ^ 6 : ℕ) : ℝ) = (Zval : ℝ) := rfl
  rw [hz]
  show (lg Zval / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (lg n + dMove μ) ≤ _
  rw [div_le_iff₀ (by linarith [lg_pos_of hn, dMove_pos μ])]
  nlinarith

/-- **The labelled cube: exact main term on both sides**, `n ≥ 2⁶⁴`. -/
theorem main_labelled_exact (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) /
        (Real.logb 2 n + 2.89) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := by
  have h3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hN : (4 : ℝ) ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact_mod_cast (by omega : 4 ≤ n)
  refine ⟨le_trans ?_ (lowerExact_labelled μ h3), godLabelled_second_order_trie μ hn⟩
  have hE := lgE_div_four
  have hnum : 0 ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1 := by
    have : (19.509 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) - 3)) ≤
        Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (((n : ℝ) + 1) * ((n : ℝ) - 3)) :=
      mul_le_mul_of_nonneg_right hE (by nlinarith)
    nlinarith
  exact div_le_div_of_nonneg_left hnum (lg_add_d_pos h3 μ) (by linarith [dMove_le μ])

/-- **The coloured cube: exact main term on both sides**, `n ≥ 2⁶⁴`. -/
theorem main_coloured_exact (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) /
        (Real.logb 2 n + 2.89) ≤ godColoured μ n ∧
    (godColoured μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := by
  have h3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hN : (100 : ℝ) ≤ n := by
    have : 2 ^ 7 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact_mod_cast (by omega : 100 ≤ n)
  refine ⟨le_trans ?_ (lowerExact_coloured μ h3), godColoured_second_order μ hn⟩
  have hZ := lgZ_div_four
  have hnum : 0 ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6 := by
    have : (12.88 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 3)) ≤
        Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * (((n : ℝ) - 1) * ((n : ℝ) - 3)) :=
      mul_le_mul_of_nonneg_right hZ (by nlinarith)
    nlinarith
  exact div_le_div_of_nonneg_left hnum (lg_add_d_pos h3 μ) (by linarith [dMove_le μ])

end RubiksGN
