import Mathlib

/-!
# Lupanov's rectangle cover

Every boolean `R × C` matrix is an exact disjoint union of rectangles of total weight
`≲ |R| |C| / log |R|`: cut the rows into blocks of `s`; within a block, group the columns by their
pattern.
-/

namespace RubiksGN

open Classical

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A rectangle. -/
abbrev Rect (α β : Type*) := Finset α × Finset β

/-- The weight of a rectangle: the length of its commutator word. -/
def Rect.cost (r : Rect α β) : ℕ := 2 * r.1.card + 2 * r.2.card + 4

/-- How many rectangles of a list contain the entry `(i, j)`. -/
noncomputable def covers (rs : List (Rect α β)) (i : α) (j : β) : ℕ :=
  rs.countP fun r => i ∈ r.1 ∧ j ∈ r.2

theorem countP_unique {γ : Type*} (l : List γ) (hl : l.Nodup) (p : γ → Bool) (a : γ) (ha : a ∈ l)
    (h : ∀ x ∈ l, p x = true ↔ x = a) : l.countP p = 1 := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.1 hl
    rcases List.mem_cons.1 ha with rfl | hat
    · have hz : t.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro y hy hpy
        have := (h y (List.mem_cons_of_mem _ hy)).1 hpy
        subst this
        exact hx hy
      rw [List.countP_cons_of_pos ((h _ List.mem_cons_self).2 rfl), hz]
    · have hnp : ¬ p x = true := by
        intro hp
        have := (h x List.mem_cons_self).1 hp
        subst this
        exact hx hat
      rw [List.countP_cons_of_neg hnp]
      exact ih ht hat (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- One block of rows: one rectangle for each pattern. -/
theorem lupanov_block (T : Finset α) (C : Finset β) (M : α → β → Prop) :
    ∃ rs : List (Rect α β), (∀ r ∈ rs, r.1 ⊆ T ∧ r.2 ⊆ C) ∧
      (∀ i ∈ T, ∀ j ∈ C, covers rs i j = if M i j then 1 else 0) ∧
      (rs.map Rect.cost).sum ≤ (2 * T.card + 4) * 2 ^ T.card + 2 * C.card := by
  let S : Finset α → Finset β := fun P => C.filter fun j => ∀ i ∈ T, (M i j ↔ i ∈ P)
  let pat : β → Finset α := fun j => T.filter fun i => M i j
  have hS : ∀ P ∈ T.powerset, ∀ j, j ∈ S P ↔ j ∈ C ∧ pat j = P := by
    intro P hP j
    have hPT := Finset.mem_powerset.1 hP
    simp only [S, pat, Finset.mem_filter]
    constructor
    · rintro ⟨hj, h⟩
      refine ⟨hj, ?_⟩
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hm⟩
        exact (h i hi).1 hm
      · intro hi
        exact ⟨hPT hi, (h i (hPT hi)).2 hi⟩
    · rintro ⟨hj, rfl⟩
      refine ⟨hj, fun i hi => ?_⟩
      simp only [Finset.mem_filter, hi, true_and]
  refine ⟨T.powerset.toList.map fun P => (P, S P), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hr
    exact ⟨Finset.mem_powerset.1 (Finset.mem_toList.1 hP), Finset.filter_subset _ _⟩
  · intro i hi j hj
    simp only [covers, List.countP_map]
    by_cases hm : M i j
    · rw [if_pos hm]
      apply countP_unique _ (Finset.nodup_toList _) _ (pat j)
      · exact Finset.mem_toList.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))
      · intro P hP
        have hP' := Finset.mem_toList.1 hP
        simp only [Function.comp, decide_eq_true_eq]
        constructor
        · rintro ⟨_, hjP⟩
          exact ((hS P hP' j).1 hjP).2.symm
        · rintro rfl
          refine ⟨?_, (hS _ hP' j).2 ⟨hj, rfl⟩⟩
          simp only [pat, Finset.mem_filter]
          exact ⟨hi, hm⟩
    · rw [if_neg hm, List.countP_eq_zero]
      intro P hP hc
      have hP' := Finset.mem_toList.1 hP
      simp only [Function.comp, decide_eq_true_eq] at hc
      obtain ⟨hiP, hjP⟩ := hc
      have := ((hS P hP' j).1 hjP).2
      subst this
      simp only [pat, Finset.mem_filter] at hiP
      exact hm hiP.2
  · rw [List.map_map]
    have : (T.powerset.toList.map (Rect.cost ∘ fun P => (P, S P))).sum =
        ∑ P ∈ T.powerset, (2 * P.card + 2 * (S P).card + 4) := by
      rw [Finset.sum_map_toList]
      rfl
    rw [this]
    have hsum : ∑ P ∈ T.powerset, (S P).card ≤ C.card := by
      have hmap : ∀ j ∈ C, pat j ∈ T.powerset := fun j _ =>
        Finset.mem_powerset.2 (Finset.filter_subset _ _)
      rw [Finset.card_eq_sum_card_fiberwise hmap]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro P hP
      congr 1
      ext j
      rw [hS P hP j, Finset.mem_filter]
    have hP : ∀ P ∈ T.powerset, 2 * P.card + 2 * (S P).card + 4 ≤
        (2 * T.card + 4) + 2 * (S P).card := by
      intro P hP
      have := Finset.card_le_card (Finset.mem_powerset.1 hP)
      omega
    calc ∑ P ∈ T.powerset, (2 * P.card + 2 * (S P).card + 4)
        ≤ ∑ P ∈ T.powerset, ((2 * T.card + 4) + 2 * (S P).card) := Finset.sum_le_sum hP
      _ = (2 * T.card + 4) * 2 ^ T.card + 2 * ∑ P ∈ T.powerset, (S P).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_powerset, smul_eq_mul,
            Finset.mul_sum, mul_comm (2 ^ T.card)]
      _ ≤ _ := by omega

/-- Lupanov's theorem: an exact cover of total weight about `2 |R| |C| / s`. -/
theorem lupanov (s : ℕ) (hs : 0 < s) (C : Finset β) (M : α → β → Prop) (R : Finset α) :
    ∃ rs : List (Rect α β), (∀ r ∈ rs, r.1 ⊆ R ∧ r.2 ⊆ C) ∧
      (∀ i ∈ R, ∀ j ∈ C, covers rs i j = if M i j then 1 else 0) ∧
      (rs.map Rect.cost).sum ≤ (R.card / s + 1) * ((2 * s + 4) * 2 ^ s + 2 * C.card) := by
  induction' hc : R.card using Nat.strong_induction_on with c ih generalizing R
  subst hc
  by_cases hlt : R.card < s
  · obtain ⟨rs, h1, h2, h3⟩ := lupanov_block R C M
    refine ⟨rs, h1, h2, h3.trans ?_⟩
    rw [Nat.div_eq_of_lt hlt]
    have hle : (2 * R.card + 4) * 2 ^ R.card ≤ (2 * s + 4) * 2 ^ s := by
      apply Nat.mul_le_mul (by omega)
      exact Nat.pow_le_pow_right (by norm_num) hlt.le
    omega
  · obtain ⟨T, hTR, hTc⟩ := Finset.exists_subset_card_eq (not_lt.1 hlt)
    obtain ⟨rs₁, a1, a2, a3⟩ := lupanov_block T C M
    have hlt' : (R \ T).card < R.card := by
      rw [Finset.card_sdiff_of_subset hTR]; omega
    obtain ⟨rs₂, b1, b2, b3⟩ := ih _ hlt' (R \ T) rfl
    refine ⟨rs₁ ++ rs₂, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact ⟨(a1 r h).1.trans hTR, (a1 r h).2⟩
      · exact ⟨(b1 r h).1.trans Finset.sdiff_subset, (b1 r h).2⟩
    · intro i hi j hj
      simp only [covers, List.countP_append] at *
      by_cases hiT : i ∈ T
      · rw [a2 i hiT j hj]
        have : rs₂.countP (fun r => decide (i ∈ r.1 ∧ j ∈ r.2)) = 0 := by
          rw [List.countP_eq_zero]
          intro r hr hc
          have := (b1 r hr).1 (of_decide_eq_true hc).1
          exact (Finset.mem_sdiff.1 this).2 hiT
        rw [this]; simp
      · rw [b2 i (Finset.mem_sdiff.2 ⟨hi, hiT⟩) j hj]
        have : rs₁.countP (fun r => decide (i ∈ r.1 ∧ j ∈ r.2)) = 0 := by
          rw [List.countP_eq_zero]
          intro r hr hc
          exact hiT ((a1 r hr).1 (of_decide_eq_true hc).1)
        rw [this]; simp
    · rw [List.map_append, List.sum_append]
      have hcard : (R \ T).card = R.card - s := by
        rw [Finset.card_sdiff_of_subset hTR, hTc]
      have hdiv : (R \ T).card / s + 1 = R.card / s := by
        rw [hcard]
        have h1 : s ≤ R.card := not_lt.1 hlt
        rw [Nat.div_eq_sub_div hs h1] 
      rw [hdiv] at b3
      rw [hTc] at a3
      calc _ ≤ (2 * s + 4) * 2 ^ s + 2 * C.card + R.card / s * ((2 * s + 4) * 2 ^ s + 2 * C.card) :=
            Nat.add_le_add a3 b3
        _ = _ := by ring

end RubiksGN
