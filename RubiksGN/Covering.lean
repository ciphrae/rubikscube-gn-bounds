import Mathlib

/-!
# The covering lemma

Let `G i j ⊆ A` be sets of at least `w` values, one for each row `i` of a set of at most `s` rows and each
column `j` of a set of at most `N` columns, with `|A| ≤ m`. Then few patterns (functions from rows to
values) suffice: at most `(m / w) ^ s * (log N + 1) + 1` patterns, such that each column has a pattern
with `p i ∈ G i j` for all rows `i`.

The proof is the greedy algorithm: each column's box of good patterns is a fraction at least
`ρ = (w / m) ^ s` of all patterns, so by averaging some pattern hits a fraction `ρ` of the columns
still uncovered.
-/

namespace RubiksGN

open Finset

section Greedy

variable {β κ : Type*} [DecidableEq β]

/-- One step of the greedy algorithm. -/
theorem greedy_step (Ω : Finset β) (U : Finset κ) (B : κ → Finset β) (ρ : ℝ)
    (hB : ∀ j ∈ U, B j ⊆ Ω) (hne : ∀ j ∈ U, (B j).Nonempty)
    (hρ : ∀ j ∈ U, ρ * (Ω.card : ℝ) ≤ ((B j).card : ℝ)) (hU : U.Nonempty) :
    ∃ p ∈ Ω, ((U.filter fun j => p ∉ B j).card : ℝ) ≤ (U.card : ℝ) * (1 - ρ) := by
  obtain ⟨j₀, hj₀⟩ := hU
  have hΩ : Ω.Nonempty := (hne j₀ hj₀).mono (hB j₀ hj₀)
  have hsum : ∑ p ∈ Ω, ((U.filter fun j => p ∈ B j).card : ℝ) = ∑ j ∈ U, ((B j).card : ℝ) := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Ω) (t := U) (fun p j => p ∈ B j)
    have h2 : ∀ j ∈ U, (Finset.bipartiteBelow (fun p j => p ∈ B j) Ω j).card = (B j).card := by
      intro j hj
      congr 1
      ext p
      simp only [Finset.mem_bipartiteBelow]
      exact ⟨fun h => h.2, fun h => ⟨hB j hj h, h⟩⟩
    rw [Finset.sum_congr rfl h2] at h
    simp only [Finset.bipartiteAbove] at h
    exact_mod_cast h
  have hle : ∑ _p ∈ Ω, ((U.card : ℝ) * ρ) ≤ ∑ p ∈ Ω, ((U.filter fun j => p ∈ B j).card : ℝ) := by
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    calc (Ω.card : ℝ) * ((U.card : ℝ) * ρ) = (U.card : ℝ) * (ρ * (Ω.card : ℝ)) := by ring
      _ = ∑ _j ∈ U, (ρ * (Ω.card : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hρ
  obtain ⟨p, hp, hpb⟩ := Finset.exists_le_of_sum_le hΩ hle
  refine ⟨p, hp, ?_⟩
  have hcard := Finset.card_filter_add_card_filter_not (s := U) (fun j => p ∈ B j)
  have hcard' : ((U.filter fun j => p ∈ B j).card : ℝ) + ((U.filter fun j => p ∉ B j).card : ℝ) =
      (U.card : ℝ) := by exact_mod_cast hcard
  nlinarith

/-- Iterating the greedy step: after `t` patterns, at most `|Y| (1 - ρ) ^ t` columns are uncovered. -/
theorem greedy_iter (Ω : Finset β) (Y : Finset κ) (B : κ → Finset β) (ρ : ℝ)
    (hB : ∀ j ∈ Y, B j ⊆ Ω) (hne : ∀ j ∈ Y, (B j).Nonempty)
    (hρ : ∀ j ∈ Y, ρ * (Ω.card : ℝ) ≤ ((B j).card : ℝ)) (hρ1 : ρ ≤ 1) (t : ℕ) :
    ∃ C : Finset β, C ⊆ Ω ∧ C.card ≤ t ∧
      ((Y.filter fun j => ∀ p ∈ C, p ∉ B j).card : ℝ) ≤ (Y.card : ℝ) * (1 - ρ) ^ t := by
  classical
  have h1ρ : 0 ≤ 1 - ρ := by linarith
  induction t with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    simp
  | succ t ih =>
    obtain ⟨C, hC, hCt, hU⟩ := ih
    set U := Y.filter fun j => ∀ p ∈ C, p ∉ B j with hUdef
    have hsub : ∀ j ∈ U, j ∈ Y := fun j hj => (Finset.mem_filter.1 hj).1
    by_cases hUe : U.Nonempty
    · obtain ⟨p, hp, hpU⟩ := greedy_step Ω U B ρ (fun j hj => hB j (hsub j hj))
        (fun j hj => hne j (hsub j hj)) (fun j hj => hρ j (hsub j hj)) hUe
      refine ⟨insert p C, Finset.insert_subset hp hC, ?_, ?_⟩
      · exact (Finset.card_insert_le _ _).trans (by omega)
      · have hset : (Y.filter fun j => ∀ q ∈ insert p C, q ∉ B j) = U.filter fun j => p ∉ B j := by
          ext j
          simp only [hUdef, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
          tauto
        rw [hset, pow_succ]
        calc _ ≤ (U.card : ℝ) * (1 - ρ) := hpU
          _ ≤ ((Y.card : ℝ) * (1 - ρ) ^ t) * (1 - ρ) := mul_le_mul_of_nonneg_right hU h1ρ
          _ = _ := by ring
    · refine ⟨C, hC, by omega, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hUe
      rw [← hUdef, hUe]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity

/-- **The greedy cover.** -/
theorem greedy_cover (Ω : Finset β) (Y : Finset κ) (B : κ → Finset β) (ρ : ℝ)
    (hB : ∀ j ∈ Y, B j ⊆ Ω) (hne : ∀ j ∈ Y, (B j).Nonempty)
    (hρ : ∀ j ∈ Y, ρ * (Ω.card : ℝ) ≤ ((B j).card : ℝ)) (hρ1 : ρ ≤ 1) (t : ℕ)
    (ht : Real.log (Y.card : ℝ) < ρ * t) :
    ∃ C : Finset β, C ⊆ Ω ∧ C.card ≤ t ∧ ∀ j ∈ Y, ∃ p ∈ C, p ∈ B j := by
  classical
  obtain ⟨C, hC, hCt, hU⟩ := greedy_iter Ω Y B ρ hB hne hρ hρ1 t
  refine ⟨C, hC, hCt, ?_⟩
  by_cases hY : Y.Nonempty
  · have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
    have h1ρ : 0 ≤ 1 - ρ := by linarith
    have hpow : (1 - ρ) ^ t ≤ Real.exp (-(ρ * t)) := by
      have h := pow_le_pow_left₀ h1ρ (Real.one_sub_le_exp_neg ρ) t
      have e : -(ρ * t) = (t : ℝ) * (-ρ) := by ring
      rw [e, Real.exp_nat_mul]
      exact h
    have hlt : (Y.card : ℝ) * Real.exp (-(ρ * t)) < 1 := by
      have h2 : Real.log (Y.card : ℝ) + -(ρ * t) < 0 := by linarith
      have h3 : Real.exp (Real.log (Y.card : ℝ) + -(ρ * t)) < 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 h2
      rwa [Real.exp_add, Real.exp_log hY0] at h3
    have hfin : ((Y.filter fun j => ∀ p ∈ C, p ∉ B j).card : ℝ) < 1 :=
      lt_of_le_of_lt (hU.trans (mul_le_mul_of_nonneg_left hpow hY0.le)) hlt
    have hzero : (Y.filter fun j => ∀ p ∈ C, p ∉ B j).card = 0 := by
      have : (Y.filter fun j => ∀ p ∈ C, p ∉ B j).card < 1 := by exact_mod_cast hfin
      omega
    rw [Finset.card_eq_zero] at hzero
    intro j hj
    by_contra hcon
    have hmem : j ∈ Y.filter fun j => ∀ p ∈ C, p ∉ B j := by
      refine Finset.mem_filter.2 ⟨hj, fun p hp hpB => hcon ⟨p, hp, hpB⟩⟩
    rw [hzero] at hmem
    simp at hmem
  · intro j hj
    exact absurd ⟨j, hj⟩ hY

end Greedy

/-- **The covering lemma.** `A` is the set of values, with `|A| ≤ m`. There are at most `s` rows and
at most `N` columns, and `G i j ⊆ A` has at least `w` values. -/
theorem covering {ι α κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : Finset α) (Y : Finset κ) (G : ι → κ → Finset α) (m w s N : ℕ) (hw : 0 < w) (hwm : w ≤ m)
    (hA : A.card ≤ m) (hι : Fintype.card ι ≤ s) (hY : Y.card ≤ N)
    (hGA : ∀ i, ∀ j ∈ Y, G i j ⊆ A) (hGw : ∀ i, ∀ j ∈ Y, w ≤ (G i j).card) :
    ∃ C : Finset (ι → α),
      (C.card : ℝ) ≤ ((m : ℝ) / w) ^ s * (Real.log (N : ℝ) + 1) + 1 ∧
        ∀ j ∈ Y, ∃ p ∈ C, ∀ i, p i ∈ G i j := by
  classical
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hwmR : (w : ℝ) ≤ m := by exact_mod_cast hwm
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  set r : ℝ := (m : ℝ) / w with hr
  have hr1 : 1 ≤ r := by rw [hr, one_le_div hw0]; exact hwmR
  have hrs : 0 < r ^ s := by positivity
  set ρ : ℝ := (r ^ s)⁻¹ with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
  set Ω : Finset (ι → α) := Fintype.piFinset fun _ => A with hΩ
  let B : κ → Finset (ι → α) := fun j => Fintype.piFinset fun i => G i j
  have hBmem : ∀ j p, p ∈ B j ↔ ∀ i, p i ∈ G i j := fun j p => Fintype.mem_piFinset
  have hBsub : ∀ j ∈ Y, B j ⊆ Ω := by
    intro j hj p hp
    rw [hBmem] at hp
    exact Fintype.mem_piFinset.2 fun i => hGA i j hj (hp i)
  have hBne : ∀ j ∈ Y, (B j).Nonempty := by
    intro j hj
    have : ∀ i, (G i j).Nonempty := fun i =>
      Finset.card_pos.1 (lt_of_lt_of_le hw (hGw i j hj))
    choose f hf using this
    exact ⟨f, (hBmem j f).2 hf⟩
  have hBcard : ∀ j ∈ Y, ρ * (Ω.card : ℝ) ≤ ((B j).card : ℝ) := by
    intro j hj
    have h1 : (Ω.card : ℝ) ≤ (m : ℝ) ^ Fintype.card ι := by
      have : Ω.card = A.card ^ Fintype.card ι := by
        simp [hΩ, Fintype.card_piFinset]
      rw [this]
      push_cast
      gcongr
    have h2 : (w : ℝ) ^ Fintype.card ι ≤ ((B j).card : ℝ) := by
      have : (B j).card = ∏ i, (G i j).card := Fintype.card_piFinset _
      rw [this]
      push_cast
      calc (w : ℝ) ^ Fintype.card ι = ∏ _i : ι, (w : ℝ) := by simp
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => hw0.le) fun i _ => by
          exact_mod_cast hGw i j hj
    have h3 : ρ * (m : ℝ) ^ Fintype.card ι ≤ (w : ℝ) ^ Fintype.card ι := by
      have h4 : r ^ Fintype.card ι ≤ r ^ s := pow_le_pow_right₀ hr1 hι
      have h5 : (m : ℝ) ^ Fintype.card ι = r ^ Fintype.card ι * (w : ℝ) ^ Fintype.card ι := by
        rw [← mul_pow, hr, div_mul_cancel₀ _ hw0.ne']
      rw [h5, hρdef, ← mul_assoc]
      have h6 : (r ^ s)⁻¹ * r ^ Fintype.card ι ≤ 1 := by
        rw [inv_mul_le_iff₀ hrs, mul_one]
        exact h4
      have h7 : (0 : ℝ) ≤ (w : ℝ) ^ Fintype.card ι := by positivity
      nlinarith
    calc ρ * (Ω.card : ℝ) ≤ ρ * (m : ℝ) ^ Fintype.card ι := mul_le_mul_of_nonneg_left h1 hρ0.le
      _ ≤ _ := h3.trans h2
  by_cases hYe : Y.Nonempty
  · set X : ℝ := r ^ s * (Real.log (N : ℝ) + 1) with hXdef
    have hX0 : 0 ≤ X := by positivity
    set t := ⌊X⌋₊ + 1 with ht
    have htX : X < t := by
      rw [ht]
      push_cast
      exact Nat.lt_floor_add_one X
    have htle : (t : ℝ) ≤ X + 1 := by
      rw [ht]
      push_cast
      linarith [Nat.floor_le hX0]
    have hlog : Real.log (Y.card : ℝ) < ρ * t := by
      have h1 : Real.log (Y.card : ℝ) ≤ Real.log (N : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hYe.card_pos
        · exact_mod_cast hY
      have h2 : ρ * X = Real.log (N : ℝ) + 1 := by
        rw [hXdef, hρdef, ← mul_assoc, inv_mul_cancel₀ hrs.ne', one_mul]
      have h3 : ρ * X < ρ * t := mul_lt_mul_of_pos_left htX hρ0
      linarith
    obtain ⟨C, _, hCt, hC⟩ := greedy_cover Ω Y B ρ hBsub hBne hBcard hρ1 t hlog
    refine ⟨C, ?_, ?_⟩
    · have : (C.card : ℝ) ≤ t := by exact_mod_cast hCt
      linarith
    · intro j hj
      obtain ⟨p, hp, hpB⟩ := hC j hj
      exact ⟨p, hp, (hBmem j p).1 hpB⟩
  · refine ⟨∅, ?_, fun j hj => absurd ⟨j, hj⟩ hYe⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end RubiksGN
