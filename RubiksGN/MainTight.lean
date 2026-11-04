import RubiksGN.ExactChain
import RubiksGN.ExactLimit
import RubiksGN.SolveExact
import RubiksGN.LowerCommute
import RubiksGN.Main

/-!
# God's number of the cube group: the exact limit

`godLabelled μ n` is the diameter of the cube group, in the half-turn or the quarter-turn slice metric. The round scheme, with the
universal lists of `RubiksGN/ExactChain.lean`, has a word length matching the counting bound:

`godLabelled μ n ~ (log₂(24!/2) / 4) · n² / log₂ n`.

The constant is `19.509…`.
-/

open Filter Topology

namespace RubiksGN

/-- The list sizes of the exact scheme. -/
abbrev exactMs : List ℕ := exactLists.map List.length

theorem exactMs_two_le : ∀ m ∈ exactMs, 2 ≤ m := by
  rw [exactMs, exactLists_sizes]
  decide

theorem exactMs_le : ∀ m ∈ exactMs, m ≤ 2 ^ 5 := by
  rw [exactMs, exactLists_sizes]
  decide

theorem exactMs_ne_nil : exactMs ≠ [] := by
  rw [exactMs, exactLists_sizes]
  decide

/-- `Σ log₂ m = 2 log₂ (24!/2)` over the list sizes. -/
theorem sumLog_exactMs :
    sumLog exactMs = 2 * Real.logb 2 (Nat.factorial 24 / 2 : ℕ) := by
  rw [sumLog, sum_logb_eq_logb_prod exactMs
    (fun m hm => by have := exactMs_two_le m hm; omega), exactLists_prod, Nat.cast_pow,
    Real.logb_pow]
  norm_num

/-- `log₂ (24!/2) / 4 ≤ 19.51`. -/
theorem lgE_div_four_le : Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 ≤ (19.51 : ℝ) := by
  have h : (Nat.factorial 24 / 2) ^ 25 ≤ 2 ^ 1951 := by decide +kernel
  have hr : (((Nat.factorial 24 / 2 : ℕ) : ℝ)) ^ 25 ≤ (2 : ℝ) ^ 1951 := by exact_mod_cast h
  have h0 : (0 : ℝ) < ((Nat.factorial 24 / 2 : ℕ) : ℝ) := by
    have : 0 < Nat.factorial 24 / 2 := by decide +kernel
    exact_mod_cast this
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  push_cast at h2 ⊢
  linarith

/-- The round scheme with the exact lists, for any admissible parameters. -/
theorem godLabelled_le_params (μ : Metric) {n : ℕ} (hn : 3 ≤ n) {S Cslot : ℕ} {sOf : ℕ → ℕ}
    (hS0 : 0 < S) (hS : Even S) (hs : ∀ m ∈ exactMs, 0 < sOf m)
    (hC : ∀ m ∈ exactMs, m ^ sOf m * (2 * sOf m * 8) ≤ Cslot) :
    (godLabelled μ n : ℝ) ≤ exactW n S Cslot sOf exactMs := by
  exact_mod_cast godLabelled_le_exactW μ hn exactLists exact_universal S hS0 hS sOf hs 8 Cslot
    exactLists_tmplLen hC

/-- **The upper bound with the exact limit constant.** -/
theorem upperLabelled_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
      (godLabelled μ n : ℝ) ≤
        (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨N, hN⟩ := exactW_limit' exactMs exactMs_two_le 8 ε hε
  refine ⟨max N 3, fun n hn μ => ?_⟩
  obtain ⟨S, C, s, h0, he, hs, hC, hW⟩ := hN n (le_trans (le_max_left _ _) hn)
  have h1 := godLabelled_le_params μ (le_trans (le_max_right _ _) hn) h0 he hs hC
  refine h1.trans (hW.trans (le_of_eq ?_))
  rw [sumLog_exactMs]
  ring

/-- The upper bound for the true God's number. -/
theorem godColoured_upper_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
      (godColoured μ n : ℝ) ≤
        (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨N, hN⟩ := upperLabelled_asymptotic ε hε
  refine ⟨max N 3, fun n hn μ => ?_⟩
  have h3 : (godColoured μ n : ℝ) ≤ godLabelled μ n := by
    exact_mod_cast godColoured_le_godLabelled μ (le_trans (le_max_right _ _) hn)
  exact h3.trans (hN n (le_trans (le_max_left _ _) hn) μ)

/-- **The limit.** The diameter of the cube group is asymptotic to `(log₂(24!/2) / 4) n² / log₂ n`. -/
theorem godLabelled_tendsto (μ : Metric) :
    Tendsto (fun n : ℕ => (godLabelled μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) atTop
      (𝓝 (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4)) := by
  rw [_root_.Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, h₁⟩ := lowerLabelled_asymptotic (ε / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := upperLabelled_asymptotic (ε / 2) (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn₃
  have hlg : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hsq : 0 < (n : ℝ) ^ 2 := by positivity
  have a := h₁ n hn₁ μ
  have b := h₂ n hn₂ μ
  rw [div_le_iff₀ hlg] at a
  rw [le_div_iff₀ hlg] at b
  have a' : Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 - ε / 2 ≤
      (godLabelled μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2 := by
    rw [le_div_iff₀ hsq]
    exact a
  have b' : (godLabelled μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2 ≤
      Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 + ε / 2 := by
    rw [div_le_iff₀ hsq]
    exact b
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### No `ε` -/

/-- `3 log₂ y ≤ y - 20` for `y ≥ 36`. -/
theorem three_lg_le {y : ℝ} (hy : 36 ≤ y) : 3 * Real.logb 2 y ≤ y - 20 := by
  have h36 : Real.logb 2 36 ≤ 5.2 := by
    have h : (36 : ℝ) ^ 5 ≤ 2 ^ 26 := by norm_num
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    push_cast at h2
    linarith
  have hy0 : 0 < y := by linarith
  have hsplit : Real.logb 2 y = Real.logb 2 36 + Real.logb 2 (y / 36) := by
    rw [← Real.logb_mul (by norm_num) (by positivity)]
    congr 1
    ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hq : 0 < y / 36 := by positivity
  have h1 : Real.log (y / 36) ≤ y / 36 - 1 := Real.log_le_sub_one_of_pos hq
  have hq1 : 0 ≤ y / 36 - 1 := by
    have : 1 ≤ y / 36 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  have h2 : Real.logb 2 (y / 36) ≤ (y / 36 - 1) / 0.69 := by
    rw [Real.logb, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  rw [hsplit]
  have h3 : (y / 36 - 1) / 0.69 = (y - 36) / 24.84 := by
    field_simp
    ring
  rw [h3] at h2
  have h4 : (y - 36) / 24.84 ≤ (y - 36) / 3 := by
    apply div_le_div_of_nonneg_left <;> linarith
  linarith

/-- The general closed form: any positive denominator below `lg n - 3 lg lg n - 11 - 256 / ⌊lg n⌋` works. -/
theorem godLabelled_le_of_denominator (μ : Metric) {n : ℕ} (hx : 36 ≤ Nat.log 2 n) {D : ℝ} (hD : 0 < D)
    (hDle : D ≤ Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 11 - 256 / (Nat.log 2 n : ℝ)) :
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 / D := by
  have h3 : 3 ≤ n := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hx
    have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
    have h4 : 2 ^ 36 ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) hx
    omega
  have hform : Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 6 - ((5 : ℕ) : ℝ) -
      32 * ((8 : ℕ) : ℝ) / (Nat.log 2 n : ℝ) =
      Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 11 - 256 / (Nat.log 2 n : ℝ) := by
    push_cast
    ring
  obtain ⟨S, C, s, h0, he, hs, hC, hW⟩ := exactW_second_order' exactMs exactMs_two_le
    exactMs_ne_nil 8 5 n exactMs_le hx (by rw [hform]; linarith)
  rw [hform, sumLog_exactMs] at hW
  have hΛ : 0 ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) := by
    have := lgE_div_four
    linarith
  have h1 := godLabelled_le_params μ h3 h0 he hs hC
  refine h1.trans (hW.trans ?_)
  have heq : 2 * Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 8 =
      Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 := by ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by positivity) hD hDle

private theorem log_facts {n k : ℕ} (hn : 2 ^ k ≤ n) :
    k ≤ Nat.log 2 n ∧ (k : ℝ) ≤ Real.logb 2 n ∧ (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  have hk' : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have h1 : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by simpa using Real.natLog_le_logb n 2
  have h2 : (k : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hk'
  exact ⟨hk', h2.trans h1, h1⟩

/-- **No `ε`, for every `n ≥ 2 ^ 36`.** -/
theorem godLabelled_second_order (μ : Metric) {n : ℕ} (hn : 2 ^ 36 ≤ n) :
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 19) := by
  obtain ⟨hx, hl, -⟩ := log_facts hn
  have hxR : (36 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hx
  have hl36 : (36 : ℝ) ≤ Real.logb 2 n := by exact_mod_cast hl
  have h3 := three_lg_le hl36
  have hfrac : 256 / (Nat.log 2 n : ℝ) ≤ 8 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact godLabelled_le_of_denominator μ hx (by linarith) (by linarith)

/-- **No `ε`, with the constant `12`, for every `n ≥ 2 ^ 256`.** Here `12 = 7 + M`, for `m ≤ 2 ^ M`, `M = 5`, and `256 = 32 L`, `L = 8`. -/
theorem godLabelled_second_order' (μ : Metric) {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 12) := by
  obtain ⟨hx, hl, -⟩ := log_facts hn
  have hxR : (256 : ℝ) ≤ (Nat.log 2 n : ℝ) := by exact_mod_cast hx
  have hl256 : (256 : ℝ) ≤ Real.logb 2 n := by exact_mod_cast hl
  have h3 := three_lg_le (by linarith : (36 : ℝ) ≤ Real.logb 2 n)
  have hfrac : 256 / (Nat.log 2 n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  exact godLabelled_le_of_denominator μ (by omega) (by linarith) (by linarith)

/-- **The tight bounds, with explicit lower-order terms and no `ε`.** The same `19.5…` on both sides. -/
theorem main_tight (μ : Metric) {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + dMove μ) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      19.51 * (n : ℝ) ^ 2 / (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 12) := by
  have h3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  refine ⟨lowerCommute_labelled μ h3, (godLabelled_second_order' μ hn).trans ?_⟩
  obtain ⟨-, hl, -⟩ := log_facts hn
  have hl256 : (256 : ℝ) ≤ Real.logb 2 n := by exact_mod_cast hl
  have h3' := three_lg_le (by linarith : (36 : ℝ) ≤ Real.logb 2 n)
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_right lgE_div_four_le (by positivity)

end RubiksGN
