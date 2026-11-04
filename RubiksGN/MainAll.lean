import RubiksGN.MainTight
import RubiksGN.MainColoured
import RubiksGN.MainTrie
import RubiksGN.MainColouredOrder

/-!
# God's number of the `n × n × n` cube: all four limits

`godLabelled μ n` is the diameter of the cube group, and `godColoured μ n` the true God's number. For both metrics `μ`, with the
value `log₂ x / 4` of the counting bound for the `x` positions of one orbit:

* `godLabelled μ n ~ (log₂(24!/2) / 4) · n² / log₂ n`,
* `godColoured μ n ~ (log₂(24!/24⁶) / 4) · n² / log₂ n`.
-/

open Filter Topology

namespace RubiksGN

/-- **All four limits.** -/
theorem main_limits (μ : Metric) :
    Tendsto (fun n : ℕ => (godLabelled μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) atTop
        (𝓝 (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4)) ∧
      Tendsto (fun n : ℕ => (godColoured μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) atTop
        (𝓝 (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4)) :=
  ⟨godLabelled_tendsto μ, godColoured_tendsto μ⟩

/-- `19.509 ≤ log₂(24!/2) / 4 ≤ 19.51`. -/
theorem lgE_bounds : (19.509 : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 ∧
    Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 ≤ 19.51 :=
  ⟨lgE_div_four, lgE_div_four_le⟩

theorem lg_add_d_pos {n : ℕ} (hn : 3 ≤ n) (μ : Metric) : 0 < Real.logb 2 n + dMove μ := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have := Real.logb_pos (by norm_num : (1 : ℝ) < 2) h1
  have := dMove_pos μ
  linarith

/-- **The labelled cube, with explicit lower-order terms.** -/
theorem main_labelled_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.89) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      19.51 * (n : ℝ) ^ 2 / (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := by
  have h3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hN : (4 : ℝ) ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact_mod_cast (by omega : 4 ≤ n)
  obtain ⟨h1, h2⟩ := main_tight' μ hn
  refine ⟨le_trans ?_ h1, h2⟩
  have hnum : 0 ≤ 19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1 := by nlinarith
  exact div_le_div_of_nonneg_left hnum (lg_add_d_pos h3 μ) (by linarith [dMove_le μ])

/-- **The coloured cube, lower bound with explicit lower-order terms.** -/
theorem main_coloured_lower (μ : Metric) (n : ℕ) (hn : 100 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured μ n := by
  have h3 : 3 ≤ n := by omega
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_trans ?_ (lowerCommute_coloured μ h3)
  have hnum : 0 ≤ 12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6 := by nlinarith
  exact div_le_div_of_nonneg_left hnum (lg_add_d_pos h3 μ) (by linarith [dMove_le μ])

/-- **The coloured cube, with explicit lower-order terms.** -/
theorem main_coloured_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured μ n ∧
    (godColoured μ n : ℝ) ≤
      12.8821 * (n : ℝ) ^ 2 / (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := by
  have h100 : 100 ≤ n := by
    have : 2 ^ 7 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  exact ⟨main_coloured_lower μ n h100, godColoured_second_order_num μ hn⟩

/-- **The lower bounds in `htm`, for every `n ≥ 3`.** -/
theorem main_lower_htm (n : ℕ) (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured .htm n ∧
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.89) ≤ godLabelled .htm n :=
  ⟨lowerCommute_coloured_htm hn, lowerCommute_labelled_htm hn⟩

/-- **The lower bounds in `qtm`, for every `n ≥ 3`.** -/
theorem main_lower_qtm (n : ℕ) (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.33) ≤ godColoured .qtm n ∧
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.33) ≤ godLabelled .qtm n :=
  ⟨lowerCommute_coloured_qtm hn, lowerCommute_labelled_qtm hn⟩

end RubiksGN
