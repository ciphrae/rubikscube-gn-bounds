import RubiksGN.Bounds

/-!
# Explicit constants

With `log₂` the logarithm in base 2:

* `n ≥ 100`: `8 n² / log₂ n ≤ godColoured μ n`,
* `n ≥ 3`: `godLabelled μ n ≤ 1800 n² / log₂ n`, and `n ≥ 100`: `godLabelled μ n ≤ 650 n² / log₂ n`,
* for every `ε > 0` and all large `n`:
  `(log₂ Z / 4 - ε) n² / log₂ n ≤ godColoured μ n` and `godLabelled μ n ≤ (275/2 + ε) n² / log₂ n`.
-/

open Real

namespace RubiksGN

variable {n : ℕ}

/-- Base-2 logarithm. -/
noncomputable abbrev lg (x : ℝ) : ℝ := Real.logb 2 x

theorem lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lg x ≤ lg y :=
  Real.logb_le_logb_of_le (by norm_num) hx hxy

theorem lg_pow (x : ℝ) (k : ℕ) : lg (x ^ k) = k * lg x := Real.logb_pow _ _ _

theorem lg_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x * y) = lg x + lg y :=
  Real.logb_mul hx hy

theorem lg_two : lg 2 = 1 := Real.logb_self_eq_one (by norm_num)

theorem lg_two_pow (k : ℕ) : lg ((2 : ℝ) ^ k) = k := by rw [lg_pow, lg_two, mul_one]

/-- `log₂ Z`. -/
noncomputable def LZ : ℝ := lg (Zval : ℝ)

theorem pow_lower_num : 2 ^ 5152 ≤ Zval ^ 100 := by decide +kernel

theorem LZ_lower : (51.52 : ℝ) ≤ LZ := by
  have h : ((2 : ℝ) ^ 5152) ≤ (Zval : ℝ) ^ 100 := by exact_mod_cast pow_lower_num
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  simp only [LZ]
  push_cast at h2
  linarith

theorem lg6_upper : lg 6 ≤ 2.6 := by
  have h : ((6 : ℝ) ^ 5) ≤ (2 : ℝ) ^ 13 := by norm_num
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  push_cast at h2
  linarith

theorem lg10_upper : lg 10 ≤ 3.33 := by
  have h : ((10 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 333 := by
    exact_mod_cast (by decide +kernel : 10 ^ 100 ≤ 2 ^ 333)
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  push_cast at h2
  linarith

theorem innerOrbits_lower (hn : 3 ≤ n) :
    ((n : ℝ) - 1) * ((n : ℝ) - 3) / 4 ≤ (innerOrbits n : ℝ) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : 2 * (m + 1) / 2 - 1 = m := by omega
    have h2 : 2 * (m + 1) - 2 * (m + 1) / 2 - 1 = m := by omega
    simp only [innerOrbits, h1, h2]
    push_cast
    nlinarith
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : (2 * (m + 1) + 1) / 2 - 1 = m := by omega
    have h2 : 2 * (m + 1) + 1 - (2 * (m + 1) + 1) / 2 - 1 = m + 1 := by omega
    simp only [innerOrbits, h1, h2]
    push_cast
    nlinarith

/-- The counting inequality in logarithmic form. -/
theorem log_count (μ : Metric) (hn : 3 ≤ n) :
    (innerOrbits n : ℝ) * LZ ≤ 15.6 + (godColoured μ n : ℝ) * (lg n + 3.33) := by
  have h := lower_count μ hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hZ : (0 : ℝ) < Zval := by
    rw [Zval_eq]; norm_num
  have h' : (Zval : ℝ) ^ innerOrbits n ≤ (6 : ℝ) ^ 6 * ((9 * n + 1 : ℝ)) ^ godColoured μ n := by
    exact_mod_cast h
  have h2 := lg_mono (by positivity) h'
  rw [lg_pow, lg_mul (by positivity) (by positivity), lg_pow, lg_pow] at h2
  have h9 : lg (9 * n + 1) ≤ lg n + 3.33 := by
    have hle : (9 * n + 1 : ℝ) ≤ 10 * n := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have := lg_mono (by positivity) hle
    rw [lg_mul (by norm_num) (by positivity)] at this
    linarith [lg10_upper]
  have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
  have h6 := lg6_upper
  push_cast at h2
  have := mul_le_mul_of_nonneg_left h9 hG
  simp only [LZ]
  nlinarith

/-- **Explicit lower bound.** -/
theorem lower_explicit (μ : Metric) (hn : 100 ≤ n) :
    8 * (n : ℝ) ^ 2 / lg n ≤ godColoured μ n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (6.6 : ℝ) ≤ lg n := by
    have h : ((2 : ℝ) ^ 33) ≤ (100 : ℝ) ^ 5 := by norm_num
    have h2 := lg_mono (by positivity) h
    rw [lg_two_pow, lg_pow] at h2
    have h3 := lg_mono (by norm_num) hN
    push_cast at h2
    linarith
  have hlc := log_count μ (by omega : 3 ≤ n)
  have hin := innerOrbits_lower (by omega : 3 ≤ n)
  have hL := LZ_lower
  have hI0 : (0 : ℝ) ≤ innerOrbits n := by positivity
  have h1 : (51.52 : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 3) / 4 ≤ (innerOrbits n : ℝ) * LZ := by
    have := mul_le_mul hin hL (by norm_num) hI0
    nlinarith
  have h2 : (12.36 : ℝ) * (n : ℝ) ^ 2 ≤ (godColoured μ n : ℝ) * (lg n + 3.33) := by
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
  have h3 : (6.6 : ℝ) * (lg n + 3.33) ≤ 9.93 * lg n := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hG
  nlinarith

/-- **The sharp lower constant.** -/
theorem lower_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric, (LZ / 4 - ε) * (n : ℝ) ^ 2 / lg n ≤ godColoured μ n := by
  by_cases hc : LZ / 4 - ε ≤ 0
  · refine ⟨2, fun n hn μ => ?_⟩
    have hx : 0 < lg n := by
      apply Real.logb_pos (by norm_num)
      exact_mod_cast (by omega : 1 < n)
    have : (LZ / 4 - ε) * (n : ℝ) ^ 2 / lg n ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc (by positivity)) hx.le
    exact this.trans (by positivity)
  · rw [not_le] at hc
    set c := LZ / 4 - ε with hcdef
    have hLpos : (0 : ℝ) < LZ := by linarith [LZ_lower]
    have htend : Filter.Tendsto (fun x : ℝ => lg x) Filter.atTop Filter.atTop :=
      Real.tendsto_logb_atTop (by norm_num)
    obtain ⟨X, hX⟩ := (Filter.eventually_ge_atTop (3.33 * c / (ε / 2) + 1)).exists_forall_of_atTop
      |> fun _ => (Filter.tendsto_atTop.1 htend (3.33 * c / (ε / 2) + 1)) |> Filter.eventually_atTop.1
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 / ε * (LZ + 16))
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge X
    refine ⟨max (max N₁ N₂) 3, fun n hn μ => ?_⟩
    have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : (N₁ : ℝ) ≤ n := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : (N₂ : ℝ) ≤ n := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hNr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hxl := hX n (hN₂.trans hn2)
    have hratio : 3.33 * c / (ε / 2) ≥ 0 := by positivity
    have hx0 : 0 < lg n := by linarith
    have hxc : 3.33 * c ≤ (lg n) * (ε / 2) := by
      have : 3.33 * c / (ε / 2) ≤ lg n := by linarith
      rwa [div_le_iff₀ (by linarith)] at this
    have hlc := log_count μ hn3
    have hin := innerOrbits_lower hn3
    have hI0 : (0 : ℝ) ≤ innerOrbits n := by positivity
    have h1 : LZ * (((n : ℝ) - 1) * ((n : ℝ) - 3) / 4) ≤ (innerOrbits n : ℝ) * LZ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hin hLpos.le
    have hnε : (LZ + 16) ≤ ε / 2 * n := by
      have := hN₁.trans hn1
      have h2 : 2 / ε * (LZ + 16) * (ε / 2) = LZ + 16 := by field_simp
      nlinarith
    have h2 : (c + ε / 2) * (n : ℝ) ^ 2 ≤ (godColoured μ n : ℝ) * (lg n + 3.33) := by
      have h3 : (c + ε / 2) = LZ / 4 - ε / 2 := by rw [hcdef]; ring
      rw [h3]
      nlinarith [mul_le_mul_of_nonneg_right hnε (by positivity : (0 : ℝ) ≤ n)]
    rw [div_le_iff₀ hx0]
    have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
    have hc' : c * (lg n + 3.33) ≤ (c + ε / 2) * lg n := by nlinarith
    have hprod : (c + ε / 2) * (n : ℝ) ^ 2 * lg n ≤
        (godColoured μ n : ℝ) * (lg n + 3.33) * lg n :=
      mul_le_mul_of_nonneg_right h2 hx0.le
    have hsum : 0 < lg n + 3.33 := by linarith
    have hkey : c * (n : ℝ) ^ 2 * (lg n + 3.33) ≤ (godColoured μ n : ℝ) * lg n * (lg n + 3.33) := by
      have : c * (n : ℝ) ^ 2 * (lg n + 3.33) ≤ (c + ε / 2) * (n : ℝ) ^ 2 * lg n := by
        have := mul_le_mul_of_nonneg_right hc' (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right hkey hsum

/-! ### Upper bounds -/

/-- The block size used for the explicit bounds. -/
def sA (n : ℕ) : ℕ := max 1 (Nat.log2 n / 2)

/-- Finite verification for small `n`. -/
def smallCheck (lo C : ℕ) : Bool :=
  (List.range 4096).all fun n =>
    decide (n < lo) || decide (upperW n (sA n) * (Nat.log2 n + 1) ≤ C * n ^ 2)

theorem smallCheck1 : smallCheck 3 1800 = true := by decide +kernel
theorem smallCheck2 : smallCheck 100 650 = true := by decide +kernel

theorem small_case {lo C : ℕ} (h : smallCheck lo C = true) (hlo : lo ≤ n) (hn : n < 4096) :
    upperW n (sA n) * (Nat.log2 n + 1) ≤ C * n ^ 2 := by
  simp only [smallCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  exact (h n hn).resolve_left (by omega)

theorem two_pow_log2_le (hn : n ≠ 0) : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn

theorem lt_two_pow_log2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self

theorem three_mul_le_two_pow (s : ℕ) (hs : 6 ≤ s) : 3 * (2 * s + 4) ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; omega

theorem L_add_le_two_pow (L : ℕ) (hL : 12 ≤ L) : 256 * (L + 2) ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ s hs ih => rw [pow_succ]; omega

/-- The analytic range of the explicit upper bound. -/
theorem large_case (hn : 4096 ≤ n) : upperW n (sA n) * (Nat.log2 n + 1) ≤ 450 * n ^ 2 := by
  set L := Nat.log2 n with hLdef
  have hn0 : n ≠ 0 := by omega
  have hLpow : 2 ^ L ≤ n := two_pow_log2_le hn0
  have hL12 : 12 ≤ L := by
    rw [hLdef]
    exact (Nat.le_log2 hn0).2 (by simpa using hn)
  set s := L / 2 with hsdef
  have hs6 : 6 ≤ s := by omega
  have hsA : sA n = s := by simp only [sA, ← hLdef]; omega
  rw [hsA]
  have h2s : 2 ^ s * 2 ^ s ≤ n := by
    calc 2 ^ s * 2 ^ s = 2 ^ (2 * s) := by rw [two_mul, pow_add]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := hLpow
  have hQ1 : 3 * ((2 * s + 4) * 2 ^ s) ≤ n := by
    calc 3 * ((2 * s + 4) * 2 ^ s) = (3 * (2 * s + 4)) * 2 ^ s := by ring
      _ ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ (three_mul_le_two_pow s hs6)
      _ ≤ n := h2s
  set r := (n / 2 - 1) / s with hrdef
  set Q := (2 * s + 4) * 2 ^ s + 2 * (n - n / 2) with hQdef
  have hQ : 3 * Q ≤ 4 * n + 3 := by omega
  have hrs : r * s ≤ n / 2 - 1 := Nat.div_mul_le_self _ _
  have hBL : 256 * (L + 2) ≤ n := (L_add_le_two_pow L hL12).trans hLpow
  have hLB : L + 1 ≤ 2 * s + 2 := by omega
  have hsB : 2 * s ≤ L := by omega
  have h12r : 12 * r ≤ n := by
    have h6r : r * 6 ≤ r * s := Nat.mul_le_mul_left r hs6
    omega
  have hup : upperW n s = 3 * n + 406 + 275 * ((r + 1) * Q) := rfl
  rw [hup]
  have hN : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  -- pass to the reals
  have rQ : (3 : ℝ) * Q ≤ 4 * n + 3 := by exact_mod_cast hQ
  have rrs : (2 : ℝ) * (r * s) ≤ n := by
    have : 2 * (r * s) ≤ n := by omega
    exact_mod_cast this
  have r12 : (12 : ℝ) * r ≤ n := by exact_mod_cast h12r
  have rB : (256 : ℝ) * (L + 2) ≤ n := by exact_mod_cast hBL
  have rLB : (L : ℝ) + 1 ≤ 2 * s + 2 := by exact_mod_cast hLB
  have rsB : (2 : ℝ) * s ≤ L := by exact_mod_cast hsB
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hA : ((r : ℝ) + 1) * (2 * s + 2) ≤ 1.18 * n := by nlinarith
  have hA2 : ((r : ℝ) + 1) * Q * (L + 1) ≤ 1.18 * n * ((4 * n + 3) / 3) := by
    have h1 : ((r : ℝ) + 1) * (L + 1) ≤ 1.18 * n := by
      refine le_trans ?_ hA
      exact mul_le_mul_of_nonneg_left rLB (by positivity)
    have h2 : (Q : ℝ) ≤ (4 * n + 3) / 3 := by linarith
    calc ((r : ℝ) + 1) * Q * (L + 1) = (((r : ℝ) + 1) * (L + 1)) * Q := by ring
      _ ≤ 1.18 * n * ((4 * n + 3) / 3) := mul_le_mul h1 h2 hQ0 (by positivity)
  have hB2 : (3 * (n : ℝ) + 406) * (L + 1) ≤ (3 * n + 406) * (n / 256) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have goal : ((3 * n + 406 + 275 * ((r + 1) * Q) : ℕ) : ℝ) * ((L : ℝ) + 1) ≤ 450 * (n : ℝ) ^ 2 := by
    push_cast
    nlinarith
  exact_mod_cast goal

/-- From the natural-number inequality to the real statement. -/
theorem real_of_nat (μ : Metric) (hn : 3 ≤ n) (s C : ℕ) (hs : 0 < s)
    (h : upperW n s * (Nat.log2 n + 1) ≤ C * n ^ 2) :
    (godLabelled μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / lg n := by
  have hN : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hx0 : 0 < lg n := Real.logb_pos (by norm_num) hN
  rw [le_div_iff₀ hx0]
  have hx : lg n ≤ Nat.log2 n + 1 := by
    have h1 : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 n + 1) := by exact_mod_cast (lt_two_pow_log2 (n := n)).le
    have h2 := lg_mono (by linarith) h1
    rw [lg_two_pow] at h2
    push_cast at h2
    exact h2
  have hG : (godLabelled μ n : ℝ) ≤ upperW n s := by
    exact_mod_cast godLabelled_le_upperW μ hn s hs
  have hh : ((upperW n s : ℝ)) * ((Nat.log2 n : ℝ) + 1) ≤ C * (n : ℝ) ^ 2 := by exact_mod_cast h
  calc (godLabelled μ n : ℝ) * lg n ≤ upperW n s * lg n :=
        mul_le_mul_of_nonneg_right hG hx0.le
    _ ≤ upperW n s * ((Nat.log2 n : ℝ) + 1) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ _ := hh

theorem sA_pos (n : ℕ) : 0 < sA n := by simp [sA]

/-- **Explicit upper bound for all `n ≥ 3`.** -/
theorem upper_explicit (μ : Metric) (hn : 3 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 1800 * (n : ℝ) ^ 2 / lg n := by
  have : upperW n (sA n) * (Nat.log2 n + 1) ≤ 1800 * n ^ 2 := by
    by_cases h : n < 4096
    · exact small_case smallCheck1 hn h
    · exact (large_case (by omega)).trans (by nlinarith [sq_nonneg n])
  exact_mod_cast real_of_nat μ hn (sA n) 1800 (sA_pos n) this

/-- **Explicit upper bound for all `n ≥ 100`.** -/
theorem upper_explicit' (μ : Metric) (hn : 100 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 650 * (n : ℝ) ^ 2 / lg n := by
  have : upperW n (sA n) * (Nat.log2 n + 1) ≤ 650 * n ^ 2 := by
    by_cases h : n < 4096
    · exact small_case smallCheck2 hn h
    · exact (large_case (by omega)).trans (by nlinarith [sq_nonneg n])
  exact_mod_cast real_of_nat μ (by omega) (sA n) 650 (sA_pos n) this

/-! ### The sharp upper constant -/

theorem succ_sq_le (b : ℕ) : (b + 1) ^ 2 ≤ 4 * 2 ^ b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    rw [pow_succ 2 b]
    rcases Nat.lt_or_ge b 2 with h | h
    · interval_cases b <;> norm_num
    · nlinarith

theorem sq_le_two_pow (L : ℕ) (hL : 4 ≤ L) : L ^ 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ 2 L]
    nlinarith

/-- The combinatorial inequality behind the sharp upper constant. -/
theorem upper_core (hn : 3 ≤ n) (L s a : ℕ) (hL4 : 4 ≤ L) (hLn : 2 ^ L ≤ n) (hsa : s + 2 * a = L)
    (ha : L < 2 ^ a) (hs : 0 < s) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ * L ≤ s) :
    ((upperW n s : ℕ) : ℝ) * ((L : ℝ) + 1) ≤
      (275 / 2 / ρ) * (n : ℝ) ^ 2 * (1 + 29 / L) + 818 * (n : ℝ) ^ 2 / L := by
  have hL2n : L ^ 2 ≤ n := (sq_le_two_pow L hL4).trans hLn
  -- the cost of the patterns is small
  have hP : (2 * s + 4) * 2 ^ s * L ≤ 3 * n := by
    have h1 : 2 ^ L = 2 ^ s * (2 ^ a * 2 ^ a) := by
      rw [← hsa, two_mul, pow_add, pow_add]
    have h2 : L * L ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul ha.le ha.le
    have h3 : (2 * s + 4) * L ≤ 3 * (L * L) := by nlinarith
    calc (2 * s + 4) * 2 ^ s * L = 2 ^ s * ((2 * s + 4) * L) := by ring
      _ ≤ 2 ^ s * (3 * (L * L)) := Nat.mul_le_mul_left _ h3
      _ ≤ 2 ^ s * (3 * (2 ^ a * 2 ^ a)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = 3 * 2 ^ L := by rw [h1]; ring
      _ ≤ 3 * n := Nat.mul_le_mul_left _ hLn
  set r := (n / 2 - 1) / s with hr
  set Q := (2 * s + 4) * 2 ^ s + 2 * (n - n / 2) with hQ
  have hrs : r * s ≤ n / 2 - 1 := Nat.div_mul_le_self _ _
  have h2rs : 2 * (r * s) ≤ n := by omega
  have hQL : Q * L ≤ 3 * n + (n + 1) * L := by
    have : 2 * (n - n / 2) ≤ n + 1 := by omega
    calc Q * L = (2 * s + 4) * 2 ^ s * L + 2 * (n - n / 2) * L := by rw [hQ]; ring
      _ ≤ 3 * n + (n + 1) * L := Nat.add_le_add hP (Nat.mul_le_mul_right _ this)
  have hup : upperW n s = 3 * n + 406 + 275 * ((r + 1) * Q) := rfl
  rw [hup]
  -- reals
  have rL4 : (4 : ℝ) ≤ L := by exact_mod_cast hL4
  have rN3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have rL2n : (L : ℝ) ^ 2 ≤ n := by exact_mod_cast hL2n
  have r2rs : (2 : ℝ) * (r * s) ≤ n := by exact_mod_cast h2rs
  have rQL : (Q : ℝ) * L ≤ 3 * n + (n + 1) * L := by exact_mod_cast hQL
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hLpos : (0 : ℝ) < L := by linarith
  have hNpos : (0 : ℝ) < n := by linarith
  have hLleN : (L : ℝ) ≤ n := by nlinarith
  have hρ1 : ρ ≤ 1 ∨ 1 < ρ := le_or_gt ρ 1
  -- 2ρL²(r+1) ≤ n(L+2) requires ρ ≤ 1 only through 2ρL² ≤ 2 s L
  have hs_le : (s : ℝ) ≤ L := by
    have : s ≤ L := by omega
    exact_mod_cast this
  have hρle : ρ ≤ 1 := by
    have : ρ * L ≤ 1 * L := by linarith
    exact le_of_mul_le_mul_right this hLpos
  have hA : 2 * ρ * (L : ℝ) ^ 2 * ((r : ℝ) + 1) ≤ n * (L + 2) := by
    have h1 : 2 * ρ * (L : ℝ) * (r : ℝ) ≤ n := by
      have := mul_le_mul_of_nonneg_right hρ hr0
      nlinarith
    have h2 : 2 * ρ * (L : ℝ) ^ 2 ≤ 2 * n := by nlinarith
    nlinarith
  have hB : (Q : ℝ) * L ≤ n * (L + 4) := by nlinarith
  have hAB : (2 * ρ * (L : ℝ) ^ 2 * ((r : ℝ) + 1)) * ((Q : ℝ) * L) ≤ (n * (L + 2)) * (n * (L + 4)) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  set P : ℝ := ((r : ℝ) + 1) * Q * ((L : ℝ) + 1) with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPL : P * (2 * ρ * (L : ℝ) ^ 3) ≤ (n : ℝ) ^ 2 * ((L : ℝ) ^ 3 + 29 * (L : ℝ) ^ 2) := by
    have h1 : P * (2 * ρ * (L : ℝ) ^ 3) =
        ((2 * ρ * (L : ℝ) ^ 2 * ((r : ℝ) + 1)) * ((Q : ℝ) * L)) * ((L : ℝ) + 1) := by
      rw [hPdef]; ring
    rw [h1]
    calc _ ≤ ((n * (L + 2)) * (n * (L + 4))) * ((L : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hAB (by positivity)
      _ = (n : ℝ) ^ 2 * ((L : ℝ) ^ 3 + 7 * (L : ℝ) ^ 2 + 14 * L + 8) := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  have hPfinal : P ≤ (n : ℝ) ^ 2 * (1 + 29 / L) / (2 * ρ) := by
    rw [le_div_iff₀ (by positivity)]
    have hLc : (0 : ℝ) < (L : ℝ) ^ 3 := by positivity
    apply le_of_mul_le_mul_right _ hLc
    have heq : (n : ℝ) ^ 2 * (1 + 29 / L) * (L : ℝ) ^ 3 =
        (n : ℝ) ^ 2 * ((L : ℝ) ^ 3 + 29 * (L : ℝ) ^ 2) := by
      field_simp
    rw [heq]
    calc P * (2 * ρ) * (L : ℝ) ^ 3 = P * (2 * ρ * (L : ℝ) ^ 3) := by ring
      _ ≤ _ := hPL
  have hsmall : (3 * (n : ℝ) + 406) * ((L : ℝ) + 1) ≤ 818 * (n : ℝ) ^ 2 / L := by
    rw [le_div_iff₀ hLpos]
    have h1 : (3 * (n : ℝ) + 406) ≤ 409 * n := by nlinarith
    have h2 : ((L : ℝ) + 1) * L ≤ 2 * n := by nlinarith
    calc (3 * (n : ℝ) + 406) * ((L : ℝ) + 1) * L = (3 * (n : ℝ) + 406) * (((L : ℝ) + 1) * L) := by ring
      _ ≤ (409 * n) * (2 * n) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 818 * (n : ℝ) ^ 2 := by ring
  push_cast
  have heq2 : (3 * (n : ℝ) + 406 + 275 * (((r : ℝ) + 1) * Q)) * ((L : ℝ) + 1) =
      (3 * (n : ℝ) + 406) * ((L : ℝ) + 1) + 275 * P := by
    rw [hPdef]; ring
  rw [heq2]
  have h275 : 275 * P ≤ (275 / 2 / ρ) * (n : ℝ) ^ 2 * (1 + 29 / L) := by
    calc 275 * P ≤ 275 * ((n : ℝ) ^ 2 * (1 + 29 / L) / (2 * ρ)) :=
          mul_le_mul_of_nonneg_left hPfinal (by norm_num)
      _ = _ := by field_simp
  linarith

/-- **The sharp upper constant.** -/
theorem upper_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric, (godLabelled μ n : ℝ) ≤ (275 / 2 + ε) * (n : ℝ) ^ 2 / lg n := by
  set e := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set η : ℝ := e / 300 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 300 := by rw [hη]; linarith
  obtain ⟨L₁, hL₁⟩ := exists_nat_ge (9640 / e)
  obtain ⟨L₂, hL₂⟩ := exists_nat_ge (16 / η ^ 2)
  refine ⟨2 ^ (L₁ + L₂ + 4), fun n hn μ => ?_⟩
  have hn4 : 16 ≤ 2 ^ (L₁ + L₂ + 4) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn3 : 3 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  set L := Nat.log2 n with hLdef
  have hLge : L₁ + L₂ + 4 ≤ L := (Nat.le_log2 hn0).2 hn
  have hL0 : L ≠ 0 := by omega
  have hLn : 2 ^ L ≤ n := two_pow_log2_le hn0
  set a := Nat.log2 L + 1 with hadef
  have hLa : L < 2 ^ a := Nat.lt_log2_self
  have hLa' : 2 ^ Nat.log2 L ≤ L := two_pow_log2_le hL0
  have hasq : a ^ 2 ≤ 4 * L := (succ_sq_le _).trans (by omega)
  have rL₁ : 9640 / e ≤ (L : ℝ) := hL₁.trans (by exact_mod_cast (by omega : L₁ ≤ L))
  have rL₂ : 16 / η ^ 2 ≤ (L : ℝ) := hL₂.trans (by exact_mod_cast (by omega : L₂ ≤ L))
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have h16 : 16 ≤ η ^ 2 * (L : ℝ) := by
    rw [div_le_iff₀ (by positivity)] at rL₂
    linarith
  have h2a : (2 : ℝ) * a ≤ η * L := by
    have h1 : ((2 : ℝ) * a) ^ 2 ≤ (η * L) ^ 2 := by
      have hr : (a : ℝ) ^ 2 ≤ 4 * L := by exact_mod_cast hasq
      have : (η * (L : ℝ)) ^ 2 = (η ^ 2 * L) * L := by ring
      rw [this]
      nlinarith
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have h2aL : 2 * a ≤ L := by
    have : (2 : ℝ) * a ≤ L := by
      refine h2a.trans ?_
      nlinarith
    exact_mod_cast this
  set s := L - 2 * a with hsdef
  have hsa : s + 2 * a = L := by omega
  have rs : (s : ℝ) = L - 2 * a := by
    have : (s : ℝ) + 2 * a = L := by exact_mod_cast hsa
    linarith
  set ρ : ℝ := 1 - η with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρs : ρ * L ≤ s := by rw [rs, hρdef]; nlinarith
  have hs0 : 0 < s := by
    have : (0 : ℝ) < s := lt_of_lt_of_le (mul_pos hρ0 hLpos) hρs
    exact_mod_cast this
  have hcore := upper_core hn3 L s a (by omega) hLn hsa hLa hs0 ρ hρ0 hρs
  have hconst : 275 / 2 / ρ ≤ 275 / 2 + e / 2 := by
    rw [div_le_iff₀ hρ0, hρdef, hη]
    nlinarith
  have hN : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hx0 : 0 < lg n := Real.logb_pos (by norm_num) hN
  rw [le_div_iff₀ hx0]
  have hx : lg n ≤ (L : ℝ) + 1 := by
    have h1 : (n : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast (Nat.lt_log2_self (n := n)).le
    have h2 := lg_mono (by linarith) h1
    rw [lg_two_pow] at h2
    push_cast at h2
    exact h2
  have hG : (godLabelled μ n : ℝ) ≤ upperW n s := by
    exact_mod_cast godLabelled_le_upperW μ hn3 s hs0
  have hN2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hdelta : 4820 / (L : ℝ) ≤ e / 2 := by
    rw [div_le_iff₀ hLpos]
    rw [div_le_iff₀ he0] at rL₁
    nlinarith
  have h29 : 0 ≤ 29 / (L : ℝ) := by positivity
  have hfinal : (275 / 2 / ρ) * (n : ℝ) ^ 2 * (1 + 29 / L) + 818 * (n : ℝ) ^ 2 / L ≤
      (275 / 2 + ε) * (n : ℝ) ^ 2 := by
    have h1 : (275 / 2 / ρ) * (1 + 29 / L) ≤ (275 / 2 + e / 2) + 138 * (29 / L) := by
      have hc0 : 0 ≤ 275 / 2 / ρ := by positivity
      have hce : e / 2 ≤ 1 / 2 := by linarith
      nlinarith
    have h2 : 818 / (L : ℝ) = 818 * (1 / L) := by ring
    have h3 : 138 * (29 / (L : ℝ)) + 818 / L = 4820 / L := by
      field_simp
      norm_num
    have h4 : (275 / 2 / ρ) * (1 + 29 / L) + 818 / (L : ℝ) ≤ 275 / 2 + ε := by
      linarith
    calc (275 / 2 / ρ) * (n : ℝ) ^ 2 * (1 + 29 / L) + 818 * (n : ℝ) ^ 2 / L
        = ((275 / 2 / ρ) * (1 + 29 / L) + 818 / (L : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 hN2
  calc (godLabelled μ n : ℝ) * lg n ≤ upperW n s * lg n :=
        mul_le_mul_of_nonneg_right hG hx0.le
    _ ≤ upperW n s * ((L : ℝ) + 1) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ _ := hcore.trans hfinal

end RubiksGN
