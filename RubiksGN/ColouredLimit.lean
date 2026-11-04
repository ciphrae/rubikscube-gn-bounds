import Mathlib
import RubiksGN.ColouredCost

/-!
# The limit of the coloured scheme's word length

With `Λ = Σ log₂ (m / w)` over the keys of the levels:

* `colouredW_limit`: for every `ε > 0` and all large `n`, suitable parameters give
  `colouredW ≤ (Λ / 8 + ε) n² / log₂ n`.

The parameters, for `x = ⌊log₂ n⌋` and `β = betaOf x` (so that `2^β x³ ≤ n`): `S = 2 x²`,
`sOf k = ⌊β / log₂ (m / w)⌋`, and `Tb k = 2^β (x + 2) + 1`. The logarithmic factor of the covering lemma
is absorbed by `β`, which need not be smaller than in `ExactLimit`: the slots cost `O(n² / x²)`.
-/

open Filter Topology

namespace RubiksGN

/-! ### Parameters, as in `ExactLimit`

`ExactLimit` cannot be imported together with the solver, because `RubiksGN.betaOf` is also a name in
`GadgetAction`. So its helpers are repeated here, in their own namespace. -/

namespace ColLim

/-- `β = x - 3 ⌊log₂ x⌋ - 3`. -/
def betaOf (x : ℕ) : ℕ := x - (3 * Nat.log 2 x + 3)

theorem three_mul_add_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 3 * k + 3 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem log_sub_le (x : ℕ) (hx : 16 ≤ x) : 3 * Nat.log 2 x + 3 ≤ x := by
  have hk : 4 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by simpa using hx)
  exact (three_mul_add_le_two_pow _ hk).trans (Nat.pow_log_le_self 2 (by omega))

theorem betaOf_pow (x : ℕ) (hx : 16 ≤ x) : 2 ^ betaOf x * x ^ 3 ≤ 2 ^ x := by
  have h := log_sub_le x hx
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
  have hcube : x ^ 3 ≤ 2 ^ (3 * Nat.log 2 x + 3) := by
    calc x ^ 3 ≤ (2 ^ (Nat.log 2 x).succ) ^ 3 := Nat.pow_le_pow_left hlt.le 3
      _ = 2 ^ (3 * Nat.log 2 x + 3) := by
        rw [← pow_mul]
        congr 1
        simp only [Nat.succ_eq_add_one]
        ring
  calc 2 ^ betaOf x * x ^ 3 ≤ 2 ^ betaOf x * 2 ^ (3 * Nat.log 2 x + 3) := Nat.mul_le_mul_left _ hcube
    _ = 2 ^ x := by
      rw [← pow_add]
      congr 1
      simp only [betaOf]
      omega

theorem betaOf_cast (x : ℕ) (hx : 16 ≤ x) :
    (betaOf x : ℝ) = (x : ℝ) - 3 * (Nat.log 2 x : ℝ) - 3 := by
  have h := log_sub_le x hx
  simp only [betaOf]
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem four_sq_le_two_pow (x : ℕ) (hx : 16 ≤ x) : 4 * x ^ 2 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ 2 x]
    nlinarith

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
    Tendsto (fun x : ℕ => ((betaOf x : ℝ) - M) / x) atTop (𝓝 1) := by
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
    Tendsto (fun x : ℕ => ((x : ℝ) + 1) / ((betaOf x : ℝ) - M)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / x) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun x : ℕ => (1 + (1 : ℝ) / x) / (((betaOf x : ℝ) - M) / x)) atTop
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

end ColLim

open ColLim

/-! ### Keys -/

/-- `log₂ (m / w)` for a key `(m, w)`. -/
noncomputable def lr (k : ℕ × ℕ) : ℝ := Real.logb 2 ((k.1 : ℝ) / k.2)

/-- `Λ = Σ log₂ (m / w)`. -/
noncomputable def sumRatio (ms : List (ℕ × ℕ)) : ℝ := (ms.map lr).sum

theorem ratio_gt_one {k : ℕ × ℕ} (h : 0 < k.2 ∧ k.2 < k.1) : 1 < (k.1 : ℝ) / k.2 := by
  have h0 : (0 : ℝ) < k.2 := by exact_mod_cast h.1
  rw [one_lt_div h0]
  exact_mod_cast h.2

theorem lr_pos {k : ℕ × ℕ} (h : 0 < k.2 ∧ k.2 < k.1) : 0 < lr k :=
  Real.logb_pos (by norm_num) (ratio_gt_one h)

theorem sumRatio_nonneg (ms : List (ℕ × ℕ)) (hms : ∀ k ∈ ms, 0 < k.2 ∧ k.2 < k.1) :
    0 ≤ sumRatio ms := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
  exact (lr_pos (hms k hk)).le

/-- The chunk size of a key. -/
noncomputable def sOfKey (β : ℕ) (k : ℕ × ℕ) : ℕ := ⌊(β : ℝ) / lr k⌋₊

theorem sOfKey_pos {β M : ℕ} {k : ℕ × ℕ} (h : 0 < lr k) (hM : lr k ≤ M) (hβ : M < β) :
    0 < sOfKey β k := by
  apply Nat.floor_pos.2
  rw [one_le_div h]
  have : (M : ℝ) < β := by exact_mod_cast hβ
  linarith

theorem sOfKey_upper {β : ℕ} {k : ℕ × ℕ} (h : 0 < lr k) : (sOfKey β k : ℝ) * lr k ≤ β := by
  have h1 := Nat.floor_le (a := (β : ℝ) / lr k) (by positivity)
  rw [le_div_iff₀ h] at h1
  exact h1

theorem sOfKey_lower {β : ℕ} {k : ℕ × ℕ} (h : 0 < lr k) : (β : ℝ) - lr k ≤ (sOfKey β k : ℝ) * lr k := by
  have h1 := Nat.lt_floor_add_one ((β : ℝ) / lr k)
  rw [div_lt_iff₀ h] at h1
  simp only [sOfKey]
  nlinarith

theorem ratio_pow_le {β : ℕ} {k : ℕ × ℕ} (h : 0 < k.2 ∧ k.2 < k.1) :
    ((k.1 : ℝ) / k.2) ^ sOfKey β k ≤ (2 : ℝ) ^ β := by
  have h0 : (0 : ℝ) < (k.1 : ℝ) / k.2 := lt_trans one_pos (ratio_gt_one h)
  have h1 := sOfKey_upper (β := β) (lr_pos h)
  have h2 : Real.logb 2 (((k.1 : ℝ) / k.2) ^ sOfKey β k) ≤ β := by
    rw [Real.logb_pow]
    exact h1
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast] at h2
  exact h2

theorem exists_nat_bound {κ : Type*} (f : κ → ℝ) (ms : List κ) : ∃ M : ℕ, ∀ k ∈ ms, f k ≤ M := by
  induction ms with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨M', hM'⟩ := exists_nat_ge (f a)
    refine ⟨max M M', ?_⟩
    intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hM'.trans (by exact_mod_cast le_max_right M M')
    · exact (hM k hk).trans (by exact_mod_cast le_max_left M M')

/-- The number of rounds with `S = 2 x²`. -/
theorem col_rounds_le (ms : List (ℕ × ℕ)) (hms : ∀ k ∈ ms, 0 < k.2 ∧ k.2 < k.1) {M β : ℕ} (x : ℕ)
    (hM : ∀ k ∈ ms, lr k ≤ M) (hMβ : M < β) :
    (colRounds (2 * x ^ 2) (sOfKey β) ms : ℝ) ≤
      (x : ℝ) ^ 2 * sumRatio ms / ((β : ℝ) - M) + ms.length := by
  have hhalf : 2 * x ^ 2 / 2 = x ^ 2 := by omega
  have hD : (0 : ℝ) < (β : ℝ) - M := by
    have : (M : ℝ) < β := by exact_mod_cast hMβ
    linarith
  induction ms with
  | nil => simp [colRounds, sumRatio]
  | cons a l ih =>
    have ih' := ih (fun m hm => hms m (by simp [hm])) (fun m hm => hM m (by simp [hm]))
    have ha := hms a (by simp)
    have hla := lr_pos ha
    have hlM := hM a (by simp)
    have hs : (0 : ℝ) < (sOfKey β a : ℝ) := by exact_mod_cast sOfKey_pos hla hlM hMβ
    have h1 : ((x ^ 2 / sOfKey β a : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 * lr a / ((β : ℝ) - M) := by
      have h2 := Nat.cast_div_le (α := ℝ) (m := x ^ 2) (n := sOfKey β a)
      refine h2.trans ?_
      push_cast
      rw [div_le_div_iff₀ hs hD]
      have h3 := sOfKey_lower (β := β) hla
      have hx : (0 : ℝ) ≤ (x : ℝ) ^ 2 := by positivity
      have h4 : (β : ℝ) - M ≤ (sOfKey β a : ℝ) * lr a := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hx]
    simp only [colRounds, sumRatio, List.map_cons, List.sum_cons, List.length_cons, hhalf] at ih' ⊢
    push_cast at ih' h1 ⊢
    rw [mul_add, add_div]
    linarith

/-- **Core estimate.** The word length, for a bound on the slots and on the number of rounds. -/
theorem colouredW_core (ms : List (ℕ × ℕ)) (sOf : ℕ × ℕ → ℕ) (Cslot n x : ℕ) (L' Rb : ℝ) (hx : 0 < x)
    (hS : 4 * x ^ 2 ≤ n) (hCs : (Cslot : ℝ) ≤ L' * n / x)
    (hR : (colRounds (2 * x ^ 2) sOf ms : ℝ) ≤ Rb) :
    (colouredW n (2 * x ^ 2) Cslot sOf ms : ℝ) ≤
      3 * n + 406 + 2200 * ((n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2)) +
        Rb * ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + L' * (n : ℝ) ^ 2 / (x : ℝ) ^ 3) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) ≤ n := by positivity
  set r := n / 2 - 1 with hr
  have hrn : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * r ≤ n := by omega
    have h : (2 : ℝ) * r ≤ n := by exact_mod_cast this
    linarith
  have hS0 : (0 : ℝ) < 2 * (x : ℝ) ^ 2 := by positivity
  have h4 : 4 * (x : ℝ) ^ 2 ≤ n := by exact_mod_cast hS
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
  have h4' : (((r ^ 2 / (2 * x ^ 2) + 2 * (r / (2 * x ^ 2) + 1) * Cslot : ℕ)) : ℝ) ≤
      (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + L' * (n : ℝ) ^ 2 / (x : ℝ) ^ 3 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
    have hmul : 2 * (((r / (2 * x ^ 2) : ℕ) : ℝ) + 1) * (Cslot : ℝ) ≤
        2 * ((n : ℝ) / (2 * (x : ℝ) ^ 2)) * (L' * (n : ℝ) / (x : ℝ)) := by
      gcongr
    have heq : 2 * ((n : ℝ) / (2 * (x : ℝ) ^ 2)) * (L' * (n : ℝ) / (x : ℝ)) =
        L' * (n : ℝ) ^ 2 / (x : ℝ) ^ 3 := by
      field_simp
    have h2c : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have h1c : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h2c, h1c]
    linarith
  have hT0 : (0 : ℝ) ≤ (colRounds (2 * x ^ 2) sOf ms : ℝ) := by positivity
  have hmain := mul_le_mul hR h4' (by positivity) (hT0.trans hR)
  have hdef : (colouredW n (2 * x ^ 2) Cslot sOf ms : ℝ) =
      3 * n + 406 + 2200 * ((r : ℝ) * (2 * (x : ℝ) ^ 2 + 2)) +
        (colRounds (2 * x ^ 2) sOf ms : ℝ) *
          (((r ^ 2 / (2 * x ^ 2) + 2 * (r / (2 * x ^ 2) + 1) * Cslot : ℕ)) : ℝ) := by
    simp only [colouredW, ← hr]
    push_cast
    ring
  rw [hdef]
  have hlast : (r : ℝ) * (2 * (x : ℝ) ^ 2 + 2) ≤ (n : ℝ) / 2 * (2 * (x : ℝ) ^ 2 + 2) := by gcongr
  linarith

/-- The bound on `colouredW / n²`. -/
noncomputable def relCol (Λ N₀ L' D : ℝ) (x : ℕ) : ℝ :=
  (Λ / D + N₀ / (x : ℝ) ^ 2) * (1 / 8 + L' / (x : ℝ)) + (2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x

theorem colouredW_scaled (ms : List (ℕ × ℕ)) (sOf : ℕ × ℕ → ℕ) (Cslot n x : ℕ) (L' Λ D : ℝ)
    (hx : 0 < x) (hS : 4 * x ^ 2 ≤ n) (hCs : (Cslot : ℝ) ≤ L' * n / x)
    (hR : (colRounds (2 * x ^ 2) sOf ms : ℝ) ≤ (x : ℝ) ^ 2 * Λ / D + ms.length) (hxn : 2 ^ x ≤ n) :
    (colouredW n (2 * x ^ 2) Cslot sOf ms : ℝ) ≤ relCol Λ ms.length L' D x * (n : ℝ) ^ 2 := by
  have h := colouredW_core ms sOf Cslot n x L' _ hx hS hCs hR
  refine h.trans ?_
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have h2x : (2 : ℝ) ^ x ≤ n := by exact_mod_cast hxn
  have h2x0 : (0 : ℝ) < (2 : ℝ) ^ x := by positivity
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ x := one_le_pow₀ (by norm_num)
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have e1 : ((x : ℝ) ^ 2 * Λ / D + ms.length) *
        ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 2) + L' * (n : ℝ) ^ 2 / (x : ℝ) ^ 3) =
      (Λ / D + ms.length / (x : ℝ) ^ 2) * (1 / 8 + L' / (x : ℝ)) * (n : ℝ) ^ 2 := by
    field_simp
  rw [e1, relCol, add_mul]
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

theorem tendsto_relCol (Λ N₀ L' : ℝ) (M : ℕ) :
    Tendsto (fun x : ℕ => ((x : ℝ) + 1) * relCol Λ N₀ L' ((betaOf x : ℝ) - M) x) atTop
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
      (((x : ℝ) + 1) / ((betaOf x : ℝ) - M) * Λ + N₀ * (((x : ℝ) + 1) / (x : ℝ) ^ 2)) *
        (1 / 8 + L' * ((1 : ℝ) / x)) +
      ((x : ℝ) + 1) * ((2609 + 2200 * (x : ℝ) ^ 2) / (2 : ℝ) ^ x)) atTop
      (𝓝 ((1 * Λ + N₀ * (0 + 0)) * (1 / 8 + L' * 0) + (2200 * 0 + 2200 * 0 + 2609 * 0 + 2609 * 0))) :=
    ((((tendsto_succ_div_D M).mul_const Λ).add (hA.const_mul N₀)).mul
      (tendsto_const_nhds.add (h1.const_mul _))).add hC
  have hval : (1 * Λ + N₀ * (0 + 0)) * (1 / 8 + L' * 0) +
      (2200 * 0 + 2200 * 0 + 2609 * 0 + 2609 * 0) = Λ / 8 := by ring
  rw [hval] at hmain
  refine hmain.congr fun x => ?_
  simp only [relCol]
  ring

/-- **The limit of the coloured scheme.** All parameters satisfy `ParamsOK` for the list of keys `ms`. -/
theorem colouredW_limit (ms : List (ℕ × ℕ)) (hms : ∀ k ∈ ms, 0 < k.2 ∧ k.2 < k.1) (L : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ (S Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ), 0 < S ∧ Even S ∧
      ParamsOK n L Cslot sOf Tb ms ∧
      (colouredW n S Cslot sOf ms : ℝ) ≤ (sumRatio ms / 8 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨M, hM⟩ := exists_nat_bound lr ms
  obtain ⟨c, hc⟩ := exists_nat_bound (fun k => (lr k)⁻¹) ms
  set L' : ℝ := 4 * c * L with hL'
  have hL'0 : 0 ≤ L' := by positivity
  have hA : sumRatio ms / 8 < sumRatio ms / 8 + ε := by linarith
  have ev1 := (tendsto_relCol (sumRatio ms) ms.length L' M).eventually_lt_const hA
  have ev2 := (tendsto_D_div M).eventually_const_lt (zero_lt_one)
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
  set β := betaOf x with hβdef
  have hD : (0 : ℝ) < (β : ℝ) - M := by
    by_contra hcon
    have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 hcon) hxR.le
    linarith
  have hMβ : M < β := by
    have h3 : (M : ℝ) < β := by linarith
    exact_mod_cast h3
  have hxn : 2 ^ x ≤ n := Nat.pow_log_le_self 2 hn0
  have hβx : β ≤ x := Nat.sub_le _ _
  have hβpow : 2 ^ β * x ^ 3 ≤ n := (betaOf_pow x h16).trans hxn
  obtain ⟨hl1, hl2⟩ := logb_bounds hn0
  rw [← hxdef] at hl1 hl2
  have hlg : 0 < Real.logb 2 (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlogn : Real.log (n : ℝ) ≤ (x : ℝ) + 1 := by
    have h3 : Real.log (n : ℝ) = Real.logb 2 n * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
    have h4 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have h5 : Real.logb 2 n * Real.log 2 ≤ Real.logb 2 n * 1 :=
      mul_le_mul_of_nonneg_left h4.le hlg.le
    linarith
  let T : ℕ := 2 ^ β * (x + 2) + 1
  let Cslot : ℕ := T * (2 * (c * β) * L)
  have hs_le : ∀ k ∈ ms, sOfKey β k ≤ c * β := by
    intro k hk
    have hk' := lr_pos (hms k hk)
    have h3 : (sOfKey β k : ℝ) ≤ (β : ℝ) / lr k := Nat.floor_le (by positivity)
    have h4 : (β : ℝ) / lr k ≤ c * β := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (hc k hk) (by positivity)
    exact_mod_cast h3.trans h4
  have hparams : ParamsOK n L Cslot (sOfKey β) (fun _ => T) ms := by
    refine ⟨fun k hk => sOfKey_pos (lr_pos (hms k hk)) (hM k hk) hMβ, ?_, ?_⟩
    · intro k hk
      have h3 := ratio_pow_le (β := β) (hms k hk)
      have h0 : (0 : ℝ) ≤ Real.log (n : ℝ) + 1 := by
        have := Real.log_natCast_nonneg n
        linarith
      have h4 := mul_le_mul h3 (show Real.log (n : ℝ) + 1 ≤ (x : ℝ) + 2 by linarith) h0
        (by positivity)
      simp only [T]
      push_cast
      linarith
    · intro k hk
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hs_le k hk)))
  have hCs : (Cslot : ℝ) ≤ L' * n / x := by
    rw [le_div_iff₀ hxR]
    have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast h16
    have hβR : (β : ℝ) ≤ x := by exact_mod_cast hβx
    have h2β : (1 : ℝ) ≤ (2 : ℝ) ^ β := one_le_pow₀ (by norm_num)
    have hT : ((T : ℕ) : ℝ) ≤ (2 : ℝ) ^ β * (2 * x) := by
      simp only [T]
      push_cast
      nlinarith
    have hb : (((2 * (c * β) * L : ℕ)) : ℝ) ≤ 2 * (c * x) * L := by
      push_cast
      gcongr
    have hpow : (2 : ℝ) ^ β * (x : ℝ) ^ 3 ≤ n := by exact_mod_cast hβpow
    calc (Cslot : ℝ) * x = (T : ℝ) * ((2 * (c * β) * L : ℕ) : ℝ) * x := by
          simp only [Cslot]
          push_cast
          ring
      _ ≤ ((2 : ℝ) ^ β * (2 * x)) * (2 * (c * x) * L) * x := by
          gcongr
      _ = L' * ((2 : ℝ) ^ β * (x : ℝ) ^ 3) := by
          rw [hL']
          ring
      _ ≤ L' * n := mul_le_mul_of_nonneg_left hpow hL'0
  have hW := colouredW_scaled ms (sOfKey β) Cslot n x L' (sumRatio ms) ((β : ℝ) - M) hx
    ((four_sq_le_two_pow x h16).trans hxn) hCs (col_rounds_le ms hms x hM hMβ) hxn
  refine ⟨2 * x ^ 2, Cslot, sOfKey β, fun _ => T, by positivity, even_two_mul _, hparams, ?_⟩
  rw [le_div_iff₀ hlg]
  set R := relCol (sumRatio ms) ms.length L' ((β : ℝ) - M) x with hR
  have hRl : R * Real.logb 2 n ≤ sumRatio ms / 8 + ε := by
    rcases le_or_gt 0 R with h0 | h0
    · have : R * Real.logb 2 n ≤ R * ((x : ℝ) + 1) := mul_le_mul_of_nonneg_left hl2.le h0
      linarith
    · have : R * Real.logb 2 n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le hlg.le
      have hΛ : 0 ≤ sumRatio ms := sumRatio_nonneg ms hms
      linarith
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc _ ≤ R * (n : ℝ) ^ 2 * Real.logb 2 n := mul_le_mul_of_nonneg_right hW hlg.le
    _ = (R * Real.logb 2 n) * (n : ℝ) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hRl hn2

end RubiksGN
