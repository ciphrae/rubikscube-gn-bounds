import Mathlib
import RubiksGN.ExactCost

/-!
# The limit of the round scheme's word length

With `Λ = Σ log₂ m` over the list sizes:

* `exactW_limit`: for every `ε > 0` and all large `n`, suitable parameters give `exactW ≤ (Λ/8 + ε) n² / log₂ n`.
* `exactW_second_order`: no `ε`: `exactW ≤ (Λ/8) n² / (log₂ n - 3 log₂ log₂ n - 7 - M)` for explicit `n`, where `m ≤ 2^M` for all
  list sizes. `exactW_second_order'` removes the hypothesis `32 L ≤ ⌊log₂ n⌋` at the cost of a term `32 L / ⌊log₂ n⌋`.
* `sum_logb_eq_logb_prod`: `Λ = log₂ ∏ m`.

The parameters are, for `x = ⌊log₂ n⌋`, `β = x - 3 ⌊log₂ x⌋ - 3` (so that `2^β x³ ≤ n`): `S = 2 x²`, `sOf m = ⌊log_m 2^β⌋`,
`Cslot = 2^β · 2 β L`.
-/

open Filter Topology

namespace RubiksGN

/-- `Λ = Σ log₂ m`. -/
noncomputable abbrev sumLog (ms : List ℕ) : ℝ := (ms.map fun m : ℕ => Real.logb 2 (m : ℝ)).sum

/-- **Goal 3.** `Σ log₂ m = log₂ ∏ m`. -/
theorem sum_logb_eq_logb_prod (ms : List ℕ) (h : ∀ m ∈ ms, 0 < m) :
    (ms.map fun m : ℕ => Real.logb 2 (m : ℝ)).sum = Real.logb 2 (ms.prod : ℕ) := by
  induction ms with
  | nil => simp
  | cons a l ih =>
    have ha : 0 < a := h a (by simp)
    have hl : ∀ m ∈ l, 0 < m := fun m hm => h m (by simp [hm])
    have hp : 0 < l.prod := List.prod_pos hl
    simp only [List.map_cons, List.sum_cons, List.prod_cons, ih hl]
    rw [Nat.cast_mul, Real.logb_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hp.ne')]

theorem one_le_logb {m : ℕ} (hm : 2 ≤ m) : 1 ≤ Real.logb 2 (m : ℝ) := by
  have h : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  simpa using h

theorem logb_le_of_le_two_pow {m M : ℕ} (hm : 2 ≤ m) (hM : m ≤ 2 ^ M) :
    Real.logb 2 (m : ℝ) ≤ M := by
  have h0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [Real.logb_le_iff_le_rpow (by norm_num) h0]
  have : (m : ℝ) ≤ (2 : ℝ) ^ M := by exact_mod_cast hM
  simpa using this

/-- From `2^β < m^(s+1)`, with `s = ⌊log_m 2^β⌋`. -/
theorem chunk_lower {m M β : ℕ} (hm : 2 ≤ m) (hM : m ≤ 2 ^ M) :
    (β : ℝ) - M ≤ (Nat.log m (2 ^ β) : ℝ) * Real.logb 2 (m : ℝ) := by
  have h := Nat.lt_pow_succ_log_self (by omega : 1 < m) (2 ^ β)
  have h0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr : ((2 : ℝ) ^ β) ≤ (m : ℝ) ^ (Nat.log m (2 ^ β)).succ := by exact_mod_cast h.le
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hr
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  have h3 := logb_le_of_le_two_pow hm hM
  push_cast at h2
  linarith

theorem chunk_pos {m M β : ℕ} (hm : 2 ≤ m) (hM : m ≤ 2 ^ M) (hMβ : M < β) :
    0 < Nat.log m (2 ^ β) :=
  Nat.log_pos (by omega) (hM.trans (Nat.pow_le_pow_right (by norm_num) hMβ.le))

theorem chunk_le (m β : ℕ) (hm : 2 ≤ m) : Nat.log m (2 ^ β) ≤ β := by
  calc Nat.log m (2 ^ β) ≤ Nat.log 2 (2 ^ β) := Nat.log_anti_left (by norm_num) hm
    _ = β := Nat.log_pow (by norm_num) β

/-- The parameters' slot bound. -/
theorem slots_le (m β L : ℕ) (hm : 2 ≤ m) :
    m ^ Nat.log m (2 ^ β) * (2 * Nat.log m (2 ^ β) * L) ≤ 2 ^ β * (2 * β * L) := by
  apply Nat.mul_le_mul (Nat.pow_log_le_self m (by positivity))
  have := chunk_le m β hm
  gcongr

/-- One list's contribution to the number of rounds. -/
theorem div_chunk_le {m M β : ℕ} (x : ℕ) (hm : 2 ≤ m) (hM : m ≤ 2 ^ M) (hMβ : M < β) :
    ((x ^ 2 / Nat.log m (2 ^ β) : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 * Real.logb 2 (m : ℝ) / ((β : ℝ) - M) := by
  have hs : (0 : ℝ) < (Nat.log m (2 ^ β) : ℝ) := by exact_mod_cast chunk_pos hm hM hMβ
  have hD : (0 : ℝ) < (β : ℝ) - M := by
    have : (M : ℝ) < β := by exact_mod_cast hMβ
    linarith
  have h1 : ((x ^ 2 / Nat.log m (2 ^ β) : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 / (Nat.log m (2 ^ β) : ℝ) := by
    have := Nat.cast_div_le (α := ℝ) (m := x ^ 2) (n := Nat.log m (2 ^ β))
    simpa using this
  refine h1.trans ?_
  rw [div_le_div_iff₀ hs hD]
  have := chunk_lower (β := β) hm hM
  have hx : (0 : ℝ) ≤ (x : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hx]

/-- The number of rounds with `S = 2 x²`. -/
theorem rounds_le (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) {M β : ℕ} (x : ℕ)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hMβ : M < β) :
    (exactRounds (2 * x ^ 2) (fun m => Nat.log m (2 ^ β)) ms : ℝ) ≤
      (x : ℝ) ^ 2 * sumLog ms / ((β : ℝ) - M) + ms.length := by
  have hhalf : 2 * x ^ 2 / 2 = x ^ 2 := by omega
  induction ms with
  | nil => simp [exactRounds, sumLog]
  | cons a l ih =>
    have ih' := ih (fun m hm => hms m (by simp [hm])) (fun m hm => hM m (by simp [hm]))
    have h1 := div_chunk_le (β := β) x (hms a (by simp)) (hM a (by simp)) hMβ
    simp only [exactRounds, sumLog, List.map_cons, List.sum_cons, List.length_cons, hhalf] at ih' ⊢
    push_cast at ih' h1 ⊢
    rw [mul_add, add_div]
    linarith

/-- **Core estimate.** The word length with explicit parameters. -/
theorem exactW_core (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (L M n x β : ℕ) (hx : 0 < x)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hMβ : M < β) (hβx : β ≤ x) (hS : 4 * x ^ 2 ≤ n)
    (hC : 2 ^ β * x ^ 3 ≤ n) :
    (exactW n (2 * x ^ 2) (2 ^ β * (2 * β * L)) (fun m => Nat.log m (2 ^ β)) ms : ℝ) ≤
      3 * n + 406 + 2200 * ((n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2)) +
        ((x : ℝ) ^ 2 * sumLog ms / ((β : ℝ) - M) + ms.length) *
          ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + 2 * L * (n : ℝ) ^ 2 / (x : ℝ) ^ 4) := by
  have hR := rounds_le ms hms x hM hMβ
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) ≤ n := by positivity
  set r := n / 2 - 1 with hr
  have hrn : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * r ≤ n := by omega
    have h : (2 : ℝ) * r ≤ n := by exact_mod_cast this
    linarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hS0 : (0 : ℝ) < 2 * (x : ℝ) ^ 2 := by positivity
  have h4 : 4 * (x : ℝ) ^ 2 ≤ n := by exact_mod_cast hS
  have hC' : (2 : ℝ) ^ β * (x : ℝ) ^ 3 ≤ n := by exact_mod_cast hC
  have hβR : (β : ℝ) ≤ x := by exact_mod_cast hβx
  -- the program part of one round
  have h1 : ((r ^ 2 / (2 * x ^ 2) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) := by
    have := Nat.cast_div_le (α := ℝ) (m := r ^ 2) (n := 2 * x ^ 2)
    push_cast at this
    refine this.trans ?_
    rw [div_le_div_iff₀ hS0 (by positivity)]
    have hsq : (r : ℝ) ^ 2 ≤ ((n : ℝ) / 2) ^ 2 := by gcongr
    have hx2 : (0 : ℝ) ≤ (x : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hsq hx2]
  have h2 : (((r / (2 * x ^ 2) : ℕ) : ℝ) + 1) ≤ (n : ℝ) / (2 * (x : ℝ) ^ 2) := by
    have := Nat.cast_div_le (α := ℝ) (m := r) (n := 2 * x ^ 2)
    push_cast at this
    have h3 : (r : ℝ) / (2 * (x : ℝ) ^ 2) ≤ (n : ℝ) / (4 * (x : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ hS0 (by positivity)]
      have hx2 : (0 : ℝ) ≤ (x : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hrn hx2]
    have h5 : (1 : ℝ) ≤ (n : ℝ) / (4 * (x : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h6 : (n : ℝ) / (2 * (x : ℝ) ^ 2) = (n : ℝ) / (4 * (x : ℝ) ^ 2) + (n : ℝ) / (4 * (x : ℝ) ^ 2) := by
      field_simp
      ring
    rw [h6]
    linarith
  have h3 : (((2 ^ β * (2 * β * L) : ℕ)) : ℝ) ≤ 2 * L * (n : ℝ) / (x : ℝ) ^ 2 := by
    push_cast
    rw [le_div_iff₀ (by positivity)]
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have h2β : (0 : ℝ) ≤ (2 : ℝ) ^ β := by positivity
    have e1 : (2 : ℝ) ^ β * (2 * (β : ℝ) * L) * (x : ℝ) ^ 2 ≤ (2 : ℝ) ^ β * (2 * (x : ℝ) * L) * (x : ℝ) ^ 2 := by
      gcongr
    have e2 : (2 : ℝ) ^ β * (2 * (x : ℝ) * L) * (x : ℝ) ^ 2 = 2 * L * ((2 : ℝ) ^ β * (x : ℝ) ^ 3) := by ring
    have e3 : 2 * (L : ℝ) * ((2 : ℝ) ^ β * (x : ℝ) ^ 3) ≤ 2 * L * n :=
      mul_le_mul_of_nonneg_left hC' (by positivity)
    linarith
  have h4' : (((r ^ 2 / (2 * x ^ 2) + 2 * (r / (2 * x ^ 2) + 1) * (2 ^ β * (2 * β * L)) : ℕ)) : ℝ) ≤
      (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + 2 * L * (n : ℝ) ^ 2 / (x : ℝ) ^ 4 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
    have hmul : 2 * (((r / (2 * x ^ 2) : ℕ) : ℝ) + 1) * (((2 ^ β * (2 * β * L) : ℕ)) : ℝ) ≤
        2 * ((n : ℝ) / (2 * (x : ℝ) ^ 2)) * (2 * L * (n : ℝ) / (x : ℝ) ^ 2) := by
      gcongr
    have heq : 2 * ((n : ℝ) / (2 * (x : ℝ) ^ 2)) * (2 * L * (n : ℝ) / (x : ℝ) ^ 2) =
        2 * L * (n : ℝ) ^ 2 / (x : ℝ) ^ 4 := by
      field_simp
    have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have h1c : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h2c, h1c]
    linarith
  have hT0 : (0 : ℝ) ≤ (exactRounds (2 * x ^ 2) (fun m => Nat.log m (2 ^ β)) ms : ℝ) := by positivity
  have hmain := mul_le_mul hR h4' (by positivity) (hT0.trans hR)
  have hdef : (exactW n (2 * x ^ 2) (2 ^ β * (2 * β * L)) (fun m => Nat.log m (2 ^ β)) ms : ℝ) =
      3 * n + 406 + 2200 * ((r : ℝ) * (2 * (x : ℝ) ^ 2 + 2)) +
        (exactRounds (2 * x ^ 2) (fun m => Nat.log m (2 ^ β)) ms : ℝ) *
          (((r ^ 2 / (2 * x ^ 2) + 2 * (r / (2 * x ^ 2) + 1) * (2 ^ β * (2 * β * L)) : ℕ)) : ℝ) := by
    simp only [exactW, ← hr]
    push_cast
    ring
  rw [hdef]
  have hlast : (r : ℝ) * (2 * (x : ℝ) ^ 2 + 2) ≤ (n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2) := by gcongr
  linarith

/-! ### The word length in terms of `x` only -/

/-- The bound on `exactW / n²`. -/
noncomputable def relBound (Λ N₀ L D : ℝ) (x : ℕ) : ℝ :=
  (Λ / D + N₀ / (x : ℝ) ^ 2) * (1 / 8 + 2 * L / (x : ℝ) ^ 2) +
    (2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x

theorem exactW_scaled (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (L M n x β : ℕ) (hx : 0 < x)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hMβ : M < β) (hβx : β ≤ x) (hS : 4 * x ^ 2 ≤ n)
    (hC : 2 ^ β * x ^ 3 ≤ n) (hxn : 2 ^ x ≤ n) :
    (exactW n (2 * x ^ 2) (2 ^ β * (2 * β * L)) (fun m => Nat.log m (2 ^ β)) ms : ℝ) ≤
      relBound (sumLog ms) ms.length L ((β : ℝ) - M) x * (n : ℝ) ^ 2 := by
  have h := exactW_core ms hms L M n x β hx hM hMβ hβx hS hC
  refine h.trans ?_
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hD : (0 : ℝ) < (β : ℝ) - M := by
    have : (M : ℝ) < β := by exact_mod_cast hMβ
    linarith
  have h2x : (2 : ℝ) ^ x ≤ n := by exact_mod_cast hxn
  have h2x0 : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ x := one_le_pow₀ (by norm_num)
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have e1 : ((x : ℝ) ^ 2 * sumLog ms / ((β : ℝ) - M) + ms.length) *
        ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + 2 * L * (n : ℝ) ^ 2 / (x : ℝ) ^ 4) =
      (sumLog ms / ((β : ℝ) - M) + ms.length / (x : ℝ) ^ 2) * (1 / 8 + 2 * L / (x : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
    field_simp
  rw [e1, relBound, add_mul]
  have e2 : 3 * (n : ℝ) + 406 + 2200 * ((n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2)) ≤
      (2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x * (n : ℝ) ^ 2 := by
    have e3 : (2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x * (n : ℝ) ^ 2 =
        ((2609 + 2200 * (x : ℝ) ^ 2) * (n : ℝ) ^ 2) / (2 : ℝ) ^ x := by ring
    rw [e3, le_div_iff₀ h2x0]
    have hx2 : (0 : ℝ) ≤ (x : ℝ) ^ 2 := by positivity
    have hG : 3 * (n : ℝ) + 406 + 2200 * ((n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2)) ≤ (2609 + 2200 * (x : ℝ) ^ 2) * n := by
      nlinarith
    calc (3 * (n : ℝ) + 406 + 2200 * ((n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2))) * (2 : ℝ) ^ x
        ≤ ((2609 + 2200 * (x : ℝ) ^ 2) * n) * n := by
          apply mul_le_mul hG h2x h2x0.le (by positivity)
      _ = _ := by ring
  linarith

/-! ### The choice of `β` -/

/-- `β = x - 3 ⌊log₂ x⌋ - 3`. -/
def expBeta (x : ℕ) : ℕ := x - (3 * Nat.log 2 x + 3)

theorem three_mul_add_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 3 * k + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem log_sub_le (x : ℕ) (hx : 16 ≤ x) : 3 * Nat.log 2 x + 3 ≤ x := by
  have hk : 4 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by simpa using hx)
  exact (three_mul_add_le_two_pow _ hk).trans (Nat.pow_log_le_self 2 (by omega))

theorem betaOf_pow (x : ℕ) (hx : 16 ≤ x) : 2 ^ expBeta x * x ^ 3 ≤ 2 ^ x := by
  have h := log_sub_le x hx
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
  have hcube : x ^ 3 ≤ 2 ^ (3 * Nat.log 2 x + 3) := by
    calc x ^ 3 ≤ (2 ^ (Nat.log 2 x).succ) ^ 3 := Nat.pow_le_pow_left hlt.le 3
      _ = 2 ^ (3 * Nat.log 2 x + 3) := by
        rw [← pow_mul]
        congr 1
        simp only [Nat.succ_eq_add_one]
        ring
  calc 2 ^ expBeta x * x ^ 3 ≤ 2 ^ expBeta x * 2 ^ (3 * Nat.log 2 x + 3) := Nat.mul_le_mul_left _ hcube
    _ = 2 ^ x := by
      rw [← pow_add]
      congr 1
      simp only [expBeta]
      omega

theorem betaOf_cast (x : ℕ) (hx : 16 ≤ x) :
    (expBeta x : ℝ) = (x : ℝ) - 3 * (Nat.log 2 x : ℝ) - 3 := by
  have h := log_sub_le x hx
  simp only [expBeta]
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem four_sq_le_two_pow (x : ℕ) (hx : 16 ≤ x) : 4 * x ^ 2 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ 2 x]
    nlinarith

/-- The parameter side conditions. -/
theorem params_ok (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) {L M β : ℕ} (x : ℕ) (hx : 0 < x)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hMβ : M < β) :
    0 < 2 * x ^ 2 ∧ Even (2 * x ^ 2) ∧ (∀ m ∈ ms, 0 < (fun m => Nat.log m (2 ^ β)) m) ∧
      (∀ m ∈ ms, m ^ (fun m => Nat.log m (2 ^ β)) m * (2 * (fun m => Nat.log m (2 ^ β)) m * L) ≤
        2 ^ β * (2 * β * L)) :=
  ⟨by positivity, even_two_mul _, fun m hm => chunk_pos (hms m hm) (hM m hm) hMβ,
    fun m hm => slots_le m β L (hms m hm)⟩

/-! ### The limit -/

theorem tendsto_natLog_div : Tendsto (fun x : ℕ => (Nat.log 2 x : ℝ) / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := h1.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h3 : Tendsto (fun x : ℕ => (Real.log x / x) / Real.log 2) atTop (𝓝 (0 / Real.log 2)) := by
    refine Tendsto.div_const ?_ _
    refine h2.congr fun x => ?_
    simp
  rw [zero_div] at h3
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) h3
  have h4 : (Nat.log 2 x : ℝ) ≤ Real.logb 2 x := by
    simpa using Real.natLog_le_logb x 2
  have h5 : Real.logb 2 (x : ℝ) = Real.log x / Real.log 2 := rfl
  rw [h5] at h4
  rw [div_right_comm]
  exact div_le_div_of_nonneg_right h4 (by positivity)

theorem tendsto_D_div (M : ℕ) :
    Tendsto (fun x : ℕ => ((expBeta x : ℝ) - M) / x) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun x : ℕ => 1 - 3 * ((Nat.log 2 x : ℝ) / x) - (3 + (M : ℝ)) * ((1 : ℝ) / x)) atTop
      (𝓝 (1 - 3 * 0 - (3 + (M : ℝ)) * 0)) :=
    (tendsto_const_nhds.sub (tendsto_natLog_div.const_mul 3)).sub (h1.const_mul _)
  have h3 : (1 - 3 * 0 - (3 + (M : ℝ)) * 0) = 1 := by ring
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 16] with x hx
  have hxR : (x : ℝ) ≠ 0 := by
    have : 0 < x := by omega
    positivity
  rw [betaOf_cast x hx]
  field_simp
  ring

theorem tendsto_succ_div_D (M : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℝ) + 1) / ((expBeta x : ℝ) - M)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun x : ℕ => (1 + (1 : ℝ) / x) / (((expBeta x : ℝ) - M) / x)) atTop
      (𝓝 ((1 + 0) / 1)) :=
    (tendsto_const_nhds.add h1).div (tendsto_D_div M) one_ne_zero
  have h3 : ((1 + 0) / 1 : ℝ) = 1 := by norm_num
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hxR : (x : ℝ) ≠ 0 := by positivity
  have e : 1 + (1 : ℝ) / x = ((x : ℝ) + 1) / x := by
    field_simp
  rw [e, div_div_div_cancel_right₀ hxR]

theorem tendsto_relBound (Λ N₀ L : ℝ) (M : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℝ) + 1) * relBound Λ N₀ L ((expBeta x : ℝ) - M) x) atTop
      (𝓝 (Λ / 8)) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun x : ℕ => ((1 : ℝ) / x) ^ 2) atTop (𝓝 (0 ^ 2)) := h1.pow 2
  rw [zero_pow two_ne_zero] at hsq
  have hA : Tendsto (fun x : ℕ => ((x : ℝ) + 1) / (x : ℝ) ^ 2) atTop (𝓝 (0 + 0)) := by
    refine (h1.add hsq).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hxR : (x : ℝ) ≠ 0 := by positivity
    field_simp
  have hE (k : ℕ) := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hC : Tendsto (fun x : ℕ => ((x : ℝ) + 1) * ((2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x)) atTop
      (𝓝 (2200 * 0 + 2200 * 0 + 2609 * 0 + 2609 * 0)) := by
    refine (((((hE 3).const_mul 2200).add ((hE 2).const_mul 2200)).add ((hE 1).const_mul 2609)).add
      ((hE 0).const_mul 2609)).congr fun x => ?_
    ring
  have hmain : Tendsto (fun x : ℕ =>
      (((x : ℝ) + 1) / ((expBeta x : ℝ) - M) * Λ + N₀ * (((x : ℝ) + 1) / (x : ℝ) ^ 2)) *
        (1 / 8 + 2 * L * ((1 : ℝ) / x) ^ 2) +
      ((x : ℝ) + 1) * ((2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x)) atTop
      (𝓝 ((1 * Λ + N₀ * (0 + 0)) * (1 / 8 + 2 * L * 0) + (2200 * 0 + 2200 * 0 + 2609 * 0 + 2609 * 0))) :=
    ((((tendsto_succ_div_D M).mul_const Λ).add (hA.const_mul N₀)).mul
      (tendsto_const_nhds.add (hsq.const_mul _))).add hC
  have hval : (1 * Λ + N₀ * (0 + 0)) * (1 / 8 + 2 * L * 0) +
      (2200 * 0 + 2200 * 0 + 2609 * 0 + 2609 * 0) = Λ / 8 := by ring
  rw [hval] at hmain
  refine hmain.congr fun x => ?_
  simp only [relBound]
  ring

theorem exists_two_pow_bound (ms : List ℕ) : ∀ m ∈ ms, m ≤ 2 ^ ms.sum := by
  intro m hm
  have h1 : m ≤ ms.sum := List.le_sum_of_mem hm
  exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) h1)

theorem length_le_sumLog (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) : (ms.length : ℝ) ≤ sumLog ms := by
  induction ms with
  | nil => simp [sumLog]
  | cons a l ih =>
    have h1 := one_le_logb (hms a (by simp))
    have h2 := ih (fun m hm => hms m (by simp [hm]))
    simp only [sumLog, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    push_cast
    linarith

/-- `x ≤ log₂ n < x + 1` for `x = ⌊log₂ n⌋`. -/
theorem logb_bounds {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ Real.logb 2 n ∧ Real.logb 2 n < (Nat.log 2 n : ℝ) + 1 := by
  refine ⟨by simpa using Real.natLog_le_logb n 2, ?_⟩
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hr : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n).succ := by exact_mod_cast h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2 := Real.logb_lt_logb (b := 2) (by norm_num) hn0 hr
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  push_cast at h2
  linarith

/-- **Goal 1.** The word length of the round scheme is at most `(Λ/8 + ε) n² / log₂ n` for all large `n`. -/
theorem exactW_limit' (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ (S Cslot : ℕ) (sOf : ℕ → ℕ), 0 < S ∧ Even S ∧ (∀ m ∈ ms, 0 < sOf m) ∧
      (∀ m ∈ ms, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) ∧
      (exactW n S Cslot sOf ms : ℝ) ≤ (sumLog ms / 8 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have hΛ : 0 ≤ sumLog ms := le_trans (by positivity) (length_le_sumLog ms hms)
  have hA : sumLog ms / 8 < sumLog ms / 8 + ε := by linarith
  have ev1 := (tendsto_relBound (sumLog ms) ms.length L ms.sum).eventually_lt_const hA
  have ev2 := (tendsto_D_div ms.sum).eventually_const_lt (zero_lt_one)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (ev1.and (ev2.and (eventually_ge_atTop 16)))
  refine ⟨2 ^ x₀, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ x₀ := by positivity
    omega
  set x := Nat.log 2 n with hxdef
  have hxx₀ : x₀ ≤ x := Nat.le_log_of_pow_le (by norm_num) hn
  obtain ⟨h1, h2, h16⟩ := hx₀ x hxx₀
  have hx : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hMβ : ms.sum < expBeta x := by
    have : (0 : ℝ) < (expBeta x : ℝ) - ms.sum := by
      by_contra hcon
      have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hxR.le
      linarith
    have h3 : (ms.sum : ℝ) < expBeta x := by linarith
    exact_mod_cast h3
  have hxn : 2 ^ x ≤ n := Nat.pow_log_le_self 2 hn0
  have hβx : expBeta x ≤ x := Nat.sub_le _ _
  have hW := exactW_scaled ms hms L ms.sum n x (expBeta x) hx (exists_two_pow_bound ms) hMβ hβx
    ((four_sq_le_two_pow x h16).trans hxn) ((betaOf_pow x h16).trans hxn) hxn
  obtain ⟨hS0, hSe, hs0, hsl⟩ := params_ok (L := L) ms hms x hx (exists_two_pow_bound ms) hMβ
  refine ⟨2 * x ^ 2, 2 ^ expBeta x * (2 * expBeta x * L), fun m => Nat.log m (2 ^ expBeta x),
    hS0, hSe, hs0, hsl, ?_⟩
  obtain ⟨hl1, hl2⟩ := logb_bounds hn0
  rw [← hxdef] at hl1 hl2
  have hlg : 0 < Real.logb 2 (n : ℝ) := by linarith
  rw [le_div_iff₀ hlg]
  set R := relBound (sumLog ms) ms.length L ((expBeta x : ℝ) - ms.sum) x with hR
  have hRl : R * Real.logb 2 n ≤ sumLog ms / 8 + ε := by
    rcases le_or_gt 0 R with h0 | h0
    · have : R * Real.logb 2 n ≤ R * ((x : ℝ) + 1) := mul_le_mul_of_nonneg_left hl2.le h0
      linarith
    · have : R * Real.logb 2 n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le hlg.le
      linarith
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc _ ≤ R * (n : ℝ) ^ 2 * Real.logb 2 n := mul_le_mul_of_nonneg_right hW hlg.le
    _ = (R * Real.logb 2 n) * (n : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hRl hn2

/-- Without a type ascription on the binder, `ms.map fun m => Real.logb 2 m` elaborates with `ms` lifted to `List ℝ`.
The value is the same. -/
theorem sum_lift (ms : List ℕ) : ((ms : List ℝ).map fun m => Real.logb 2 m).sum = sumLog ms := by
  induction ms with
  | nil => simp [sumLog]
  | cons a l ih =>
    simp only [sumLog] at ih ⊢
    simpa using ih

set_option linter.unusedVariables false in
/-- `exactW_limit'` with the sum written as in the plan (binder type left to elaboration). -/
theorem exactW_limit (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ (S Cslot : ℕ) (sOf : ℕ → ℕ), 0 < S ∧ Even S ∧ (∀ m ∈ ms, 0 < sOf m) ∧
      (∀ m ∈ ms, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) ∧
      (exactW n S Cslot sOf ms : ℝ) ≤
        ((ms.map fun m => Real.logb 2 m).sum / 8 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  rw [sum_lift]
  exact exactW_limit' ms hms L ε hε

/-! ### Second order -/

theorem poly_le_two_pow (x : ℕ) (hx : 36 ≤ x) : 8 * x ^ 2 * (2609 + 2200 * x ^ 2) ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ 2 x]
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hx
    refine le_trans ?_ (Nat.mul_le_mul_right 2 ih)
    ring_nf
    nlinarith [Nat.zero_le y, Nat.zero_le (y ^ 2), Nat.zero_le (y ^ 3), Nat.zero_le (y ^ 4)]

theorem rel_aux (Λ N₀ L D X E : ℝ) (hX : 1 ≤ X) (hL0 : 0 ≤ L) (hD : 2 + 32 * L / X < D)
    (hDX : D ≤ X) (hΛ : 1 ≤ Λ) (hN : N₀ ≤ Λ) (hE : 8 * X ^ 2 * E ≤ 1) :
    (Λ / D + N₀ / X ^ 2) * (1 / 8 + 2 * L / X ^ 2) + E ≤ (Λ / 8) / (D - 2 - 32 * L / X) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = 32 * L / X := ⟨_, rfl⟩
  rw [← ha] at hD ⊢
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hD0 : 0 < D := by linarith
  have hD3 : 0 < D - 2 - a := by linarith
  obtain ⟨i, hi⟩ : ∃ i, i = 1 / X := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 1 / D := ⟨_, rfl⟩
  have hi0 : 0 < i := by rw [hi]; positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  have hiX : i * X = 1 := by rw [hi]; field_simp
  have hi1 : i ≤ 1 := by
    rw [hi, div_le_one hX0]
    exact hX
  have hit : i ≤ t := by
    rw [hi, ht]
    exact one_div_le_one_div_of_le hD0 hDX
  have e1 : Λ / D = Λ * t := by rw [ht]; ring
  have e2 : N₀ / X ^ 2 = N₀ * i ^ 2 := by rw [hi]; ring
  have e3 : 2 * L / X ^ 2 = 1 / 8 * (a / 2 * i) := by rw [hi, ha]; field_simp; ring
  rw [e1, e2, e3]
  have hA : Λ * t + N₀ * i ^ 2 ≤ Λ * t * (1 + i) := by
    have h1 : N₀ * i ^ 2 ≤ Λ * i ^ 2 := mul_le_mul_of_nonneg_right hN (by positivity)
    have h2 : Λ * i ^ 2 ≤ Λ * (t * i) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hit hi0.le
    nlinarith
  have hC : E ≤ Λ * (t * i) / 8 := by
    have h1 : 8 * E ≤ i ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_right hE (by positivity : 0 ≤ i ^ 2)
      have h3 : 8 * X ^ 2 * E * i ^ 2 = 8 * E * (i * X) ^ 2 := by ring
      rw [h3, hiX] at h2
      linarith
    have h2 : i ^ 2 ≤ t * i := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hit hi0.le
    have h3 : t * i ≤ Λ * (t * i) := by
      have : 0 ≤ t * i := by positivity
      nlinarith
    linarith
  have hprod : (Λ * t + N₀ * i ^ 2) * (1 / 8 + 1 / 8 * (a / 2 * i)) ≤
      Λ * t * (1 + i) * (1 / 8 + 1 / 8 * (a / 2 * i)) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have hF : t * (1 + (2 + a) * i) ≤ 1 / (D - 2 - a) := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hD0 hD3]
    have h1 : i * (D - 2 - a) ≤ 1 := by
      have h2 : i * (D - 2 - a) ≤ i * X := mul_le_mul_of_nonneg_left (by linarith) hi0.le
      linarith
    have h3 : 0 ≤ (2 + a) * (1 - i * (D - 2 - a)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hfin : (Λ / 8) / (D - 2 - a) = Λ / 8 * (1 / (D - 2 - a)) := by ring
  rw [hfin]
  have hΛ8 : 0 ≤ Λ / 8 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hF hΛ8
  have hkey : Λ * t * (1 + i) * (1 / 8 + 1 / 8 * (a / 2 * i)) + Λ * (t * i) / 8 ≤
      Λ / 8 * (t * (1 + (2 + a) * i)) := by
    have h2 : Λ * t * (1 + i) * (1 / 8 + 1 / 8 * (a / 2 * i)) + Λ * (t * i) / 8 =
        Λ / 8 * (t * (1 + 2 * i + a / 2 * i + a / 2 * i ^ 2)) := by ring
    rw [h2]
    apply mul_le_mul_of_nonneg_left _ hΛ8
    apply mul_le_mul_of_nonneg_left _ ht0.le
    have h3 : a / 2 * i ^ 2 ≤ a / 2 * i := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith
  linarith

/-- **Goal 2, general form.** No `ε`. `M` bounds the list sizes: `m ≤ 2 ^ M`. -/
theorem exactW_second_order' (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (hne : ms ≠ []) (L M n : ℕ)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hx36 : 36 ≤ Nat.log 2 n)
    (hD : 0 < Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 6 - M - 32 * L / (Nat.log 2 n : ℝ)) :
    ∃ (S Cslot : ℕ) (sOf : ℕ → ℕ), 0 < S ∧ Even S ∧ (∀ m ∈ ms, 0 < sOf m) ∧
      (∀ m ∈ ms, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) ∧
      (exactW n S Cslot sOf ms : ℝ) ≤
        (sumLog ms / 8) * (n : ℝ) ^ 2 /
          (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 6 - M - 32 * L / (Nat.log 2 n : ℝ)) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hx36
  set x := Nat.log 2 n with hxdef
  have h16 : 16 ≤ x := by omega
  have hx : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨hl1, hl2⟩ := logb_bounds hn0
  rw [← hxdef] at hl1 hl2
  have hlog : (Nat.log 2 x : ℝ) ≤ Real.logb 2 (Real.logb 2 n) := by
    have h1 : (Nat.log 2 x : ℝ) ≤ Real.logb 2 x := by simpa using Real.natLog_le_logb x 2
    exact h1.trans (Real.logb_le_logb_of_le (by norm_num) hxR hl1)
  have hβ := betaOf_cast x h16
  have ha0 : 0 ≤ 32 * (L : ℝ) / x := by positivity
  set D₀ := Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 6 - M - 32 * L / (x : ℝ) with hD₀
  have hDD : D₀ ≤ (expBeta x : ℝ) - M - 2 - 32 * L / x := by
    rw [hβ, hD₀]
    linarith
  have hMβ : M < expBeta x := by
    have h3 : (M : ℝ) < expBeta x := by linarith
    exact_mod_cast h3
  have hxn : 2 ^ x ≤ n := Nat.pow_log_le_self 2 hn0
  have hβx : expBeta x ≤ x := Nat.sub_le _ _
  have hW := exactW_scaled ms hms L M n x (expBeta x) hx hM hMβ hβx
    ((four_sq_le_two_pow x h16).trans hxn) ((betaOf_pow x h16).trans hxn) hxn
  obtain ⟨hS0, hSe, hs0, hsl⟩ := params_ok (L := L) ms hms x hx hM hMβ
  refine ⟨2 * x ^ 2, 2 ^ expBeta x * (2 * expBeta x * L), fun m => Nat.log m (2 ^ expBeta x),
    hS0, hSe, hs0, hsl, ?_⟩
  have hlen := length_le_sumLog ms hms
  have h1len : (1 : ℝ) ≤ ms.length := by
    have : 1 ≤ ms.length := List.length_pos_iff.2 hne
    exact_mod_cast this
  have hE : 8 * (x : ℝ) ^ 2 * ((2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x) ≤ 1 := by
    have h := poly_le_two_pow x hx36
    have hr : 8 * (x : ℝ) ^ 2 * (2609 + 2200 * (x : ℝ) ^ 2) ≤ (2 : ℝ) ^ x := by exact_mod_cast h
    rw [← mul_div_assoc, div_le_one (by positivity)]
    exact hr
  have hDx : (expBeta x : ℝ) - M ≤ x := by
    have h1 : (expBeta x : ℝ) ≤ x := by exact_mod_cast hβx
    have h2 : (0 : ℝ) ≤ M := by positivity
    linarith
  have hrel := rel_aux (sumLog ms) ms.length L ((expBeta x : ℝ) - M) x
    ((2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x)
    (by exact_mod_cast hx) (by positivity) (by linarith) hDx
    (by linarith) hlen hE
  have hmono : (sumLog ms / 8) / ((expBeta x : ℝ) - M - 2 - 32 * L / x) ≤ (sumLog ms / 8) / D₀ :=
    div_le_div_of_nonneg_left (by linarith) hD hDD
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc _ ≤ relBound (sumLog ms) ms.length L ((expBeta x : ℝ) - M) x * (n : ℝ) ^ 2 := hW
    _ ≤ (sumLog ms / 8) / D₀ * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (hrel.trans hmono) hn2
    _ = _ := by ring

/-- **Goal 2.** The clean form, when `n ≥ 2 ^ (32 L)`. -/
theorem exactW_second_order (ms : List ℕ) (hms : ∀ m ∈ ms, 2 ≤ m) (hne : ms ≠ []) (L M n : ℕ)
    (hM : ∀ m ∈ ms, m ≤ 2 ^ M) (hx36 : 36 ≤ Nat.log 2 n) (hLx : 32 * L ≤ Nat.log 2 n)
    (hD : 0 < Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7 - M) :
    ∃ (S Cslot : ℕ) (sOf : ℕ → ℕ), 0 < S ∧ Even S ∧ (∀ m ∈ ms, 0 < sOf m) ∧
      (∀ m ∈ ms, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) ∧
      (exactW n S Cslot sOf ms : ℝ) ≤
        (sumLog ms / 8) * (n : ℝ) ^ 2 /
          (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7 - M) := by
  have hxR : (0 : ℝ) < (Nat.log 2 n : ℝ) := by exact_mod_cast (by omega : 0 < Nat.log 2 n)
  have ha : 32 * (L : ℝ) / (Nat.log 2 n : ℝ) ≤ 1 := by
    rw [div_le_one hxR]
    exact_mod_cast hLx
  obtain ⟨S, C, s, h1, h2, h3, h4, h5⟩ := exactW_second_order' ms hms hne L M n hM hx36 (by linarith)
  refine ⟨S, C, s, h1, h2, h3, h4, h5.trans ?_⟩
  have hΛ : 0 ≤ sumLog ms := le_trans (by positivity) (length_le_sumLog ms hms)
  exact div_le_div_of_nonneg_left (by positivity) hD (by linarith)

end RubiksGN
