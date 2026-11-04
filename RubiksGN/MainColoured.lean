import RubiksGN.ColourCheck
import RubiksGN.ColouredBound
import RubiksGN.Constants

/-!
# God's number of the coloured cube: the exact limit

`godColoured μ n` is the true God's number of the `n × n × n` cube (positions are colourings). The round scheme with the colour
lists of `RubiksGN/ColourData.lean` matches the counting bound:

`godColoured μ n ~ (log₂(24!/24⁶) / 4) · n² / log₂ n`.

The constant is `12.88…`.
-/

open Filter Topology

namespace RubiksGN

theorem colourData_valid : colourData.Valid := ColourData.valid_of_check colourData_check

/-- The keys of the colour lists. -/
theorem colourData_keys : colourData.keys = [(24, 4), (24, 4), (23, 4), (23, 4), (22, 4), (22, 4), (21, 4), (21, 4), (20, 3),
    (20, 3), (19, 4), (18, 4), (17, 3), (16, 3), (15, 3), (14, 2), (13, 1), (12, 2), (11, 2), (10, 2), (9, 1), (8, 3), (7, 3),
    (6, 2), (19, 4), (18, 3), (17, 4), (16, 3), (15, 3), (14, 2), (13, 3), (12, 3), (11, 1), (10, 2), (9, 1), (8, 2), (7, 2),
    (6, 2), (12, 1), (5, 1), (12, 1), (5, 1)] := by
  decide +kernel

/-- `∏ m = Z² ∏ w` over the keys, with `Z = 24! / 24⁶`. -/
theorem colourData_prod : (colourData.keys.map Prod.fst).prod =
    (Nat.factorial 24 / 24 ^ 6) ^ 2 * (colourData.keys.map Prod.snd).prod := by
  rw [colourData_keys]
  decide +kernel

/-- `Λ` is the difference of the logarithms of the two products. -/
theorem sumRatio_eq_sub (ms : List (ℕ × ℕ)) (h : ∀ k ∈ ms, 0 < k.1 ∧ 0 < k.2) :
    sumRatio ms = Real.logb 2 ((ms.map Prod.fst).prod : ℕ) - Real.logb 2 ((ms.map Prod.snd).prod : ℕ) := by
  induction ms with
  | nil => simp [sumRatio]
  | cons a l ih =>
    obtain ⟨ha1, ha2⟩ := h a (by simp)
    have hl : ∀ k ∈ l, 0 < k.1 ∧ 0 < k.2 := fun k hk => h k (by simp [hk])
    have hp1 : 0 < (l.map Prod.fst).prod := List.prod_pos fun m hm => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hm
      exact (hl k hk).1
    have hp2 : 0 < (l.map Prod.snd).prod := List.prod_pos fun m hm => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hm
      exact (hl k hk).2
    have ih' := ih hl
    simp only [sumRatio, List.map_cons, List.sum_cons, List.prod_cons, lr] at ih' ⊢
    rw [ih', Nat.cast_mul, Nat.cast_mul,
      Real.logb_mul (by exact_mod_cast ha1.ne') (by exact_mod_cast hp1.ne'),
      Real.logb_mul (by exact_mod_cast ha2.ne') (by exact_mod_cast hp2.ne'),
      Real.logb_div (by exact_mod_cast ha1.ne') (by exact_mod_cast ha2.ne')]
    ring

/-- **`Λ = 2 log₂ Z`**, exactly. -/
theorem sumRatio_colourData :
    sumRatio colourData.keys = 2 * Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) := by
  have hk : ∀ k ∈ colourData.keys, 0 < k.1 ∧ 0 < k.2 := fun k hk => by
    have := colourData_valid.keys_lt k hk
    omega
  have hZ : 0 < Nat.factorial 24 / 24 ^ 6 := by decide +kernel
  have hw : 0 < (colourData.keys.map Prod.snd).prod := List.prod_pos fun m hm => by
    obtain ⟨k, hk', rfl⟩ := List.mem_map.1 hm
    exact (hk k hk').2
  rw [sumRatio_eq_sub _ hk, colourData_prod, Nat.cast_mul, Nat.cast_pow,
    Real.logb_mul (pow_ne_zero _ (by exact_mod_cast hZ.ne')) (by exact_mod_cast hw.ne'), Real.logb_pow]
  push_cast
  ring

/-- **The upper bound with the exact limit constant.** -/
theorem upperColoured_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric, (godColoured μ n : ℝ) ≤
      (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := by
  obtain ⟨N, hN⟩ := colouredW_limit colourData.keys colourData_valid.keys_lt colourData.L ε hε
  refine ⟨max N 3, fun n hn μ => ?_⟩
  obtain ⟨S, Cslot, sOf, Tb, hS0, hS, hp, hW⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hle := godColoured_le_colouredW μ (le_trans (le_max_right _ _) hn) colourData colourData_valid S
    Cslot sOf Tb hS0 hS hp
  refine le_trans (by exact_mod_cast hle) (hW.trans (le_of_eq ?_))
  rw [sumRatio_colourData]
  ring_nf

/-- **The limit.** God's number of the coloured cube is asymptotic to `(log₂(24!/24⁶) / 4) n² / log₂ n`. -/
theorem godColoured_tendsto (μ : Metric) :
    Tendsto (fun n : ℕ => (godColoured μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) atTop
      (𝓝 (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4)) := by
  rw [_root_.Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, h₁⟩ := lower_asymptotic (ε / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := upperColoured_asymptotic (ε / 2) (by linarith)
  refine ⟨max (max N₁ N₂) 2, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₃ : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn₃
  have hlg : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) (by linarith)
  have hsq : 0 < (n : ℝ) ^ 2 := by positivity
  have a : (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 - ε / 2) * (n : ℝ) ^ 2 / Real.logb 2 n ≤
      godColoured μ n := h₁ n hn₁ μ
  have b := h₂ n hn₂ μ
  rw [div_le_iff₀ hlg] at a
  rw [le_div_iff₀ hlg] at b
  have a' : Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 - ε / 2 ≤
      (godColoured μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2 := by
    rw [le_div_iff₀ hsq]
    exact a
  have b' : (godColoured μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2 ≤
      Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 + ε / 2 := by
    rw [div_le_iff₀ hsq]
    exact b
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end RubiksGN
