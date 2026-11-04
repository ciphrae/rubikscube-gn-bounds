import RubiksGN.UnivData

/-!
# Every even permutation of an orbit is a subproduct of one fixed sequence of letters

`uSeq` is a fixed list of 275 letters. Every even permutation of the 24 coordinates of an orbit is the
product of a sublist of `uSeq`; the proof follows a stabilizer chain verified by the kernel.
-/

open Equiv

namespace RubiksGN

/-- The product of a list of letters. -/
def prodL (T : List Letter) : Perm (Fin 24) := (T.map lp).prod

/-- Decidable check of one level. -/
def levelOK (fixed : List (Fin 24)) (l : ULevel) : Bool :=
  !fixed.contains l.1 &&
  (List.finRange 24).all fun x =>
    fixed.contains x ||
      match l.2.2.lookup x with
      | none => false
      | some T => decide (T.Sublist l.2.1) && decide (prodL T l.1 = x) &&
          fixed.all fun f => decide (prodL T f = f)

/-- Decidable check of a whole chain. -/
def chainOK : List (Fin 24) → List ULevel → Bool
  | fixed, [] => (List.finRange 24).all fun x => fixed.contains x || x == uLastA || x == uLastB
  | fixed, l :: ls => levelOK fixed l && chainOK (l.1 :: fixed) ls

theorem uChain_ok : chainOK [] uChain = true := by decide +kernel

theorem uLast_ne : uLastA ≠ uLastB := by decide

theorem sign_cyc3 : ∀ L : Letter, Perm.sign (lp L) = 1 := by
  rintro ⟨τ, da, db, f⟩
  have hd : ∀ (τ : Fin 24) (da db : Bool), τ ≠ mul τ (alphaOf da) ∧
      mul τ (alphaOf da) ≠ mul τ (betaOf db) := by
    decide +kernel
  obtain ⟨h1, h2⟩ := hd τ da db
  have hc : Perm.sign (cyc3 τ (mul τ (alphaOf da)) (mul τ (betaOf db))) = 1 := by
    simp [cyc3, Perm.sign_swap h1, Perm.sign_swap h2]
  cases f <;> simp [lp, hc]

theorem sign_prodL (T : List Letter) : Perm.sign (prodL T) = 1 := by
  induction T with
  | nil => simp [prodL]
  | cons L t ih =>
    simp only [prodL, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih, sign_cyc3]; rfl

theorem prodL_append (S T : List Letter) : prodL (S ++ T) = prodL S * prodL T := by
  simp [prodL]

theorem even_last (fixed : List (Fin 24))
    (h : ∀ x : Fin 24, x ∈ fixed ∨ x = uLastA ∨ x = uLastB) (π : Perm (Fin 24))
    (hs : Perm.sign π = 1) (hf : ∀ f ∈ fixed, π f = f) : π = 1 := by
  have hne := uLast_ne
  have key : ∀ x y, π x = y → y ∈ fixed → x = y := fun x y hxy hy =>
    π.injective (by rw [hxy, hf y hy])
  have hA : π uLastA = uLastA := by
    by_contra hna
    have hy : π uLastA = uLastB := by
      rcases h (π uLastA) with hy | hy | hy
      · exact absurd (key _ _ rfl hy).symm hna
      · exact absurd hy hna
      · exact hy
    have hb : π uLastB = uLastA := by
      rcases h (π uLastB) with hz | hz | hz
      · have := (key _ _ rfl hz).symm
        exact absurd (π.injective (hy.trans this.symm)) hne
      · exact hz
      · exact absurd (π.injective (hy.trans hz.symm)) hne
    have hsw : π = swap uLastA uLastB := by
      apply Equiv.ext
      intro x
      rcases h x with hx | rfl | rfl
      · rw [hf x hx, swap_apply_of_ne_of_ne]
        · rintro rfl
          exact hna (hf _ hx)
        · rintro rfl
          exact hne (hb.symm.trans (hf _ hx))
      · rw [hy, swap_apply_left]
      · rw [hb, swap_apply_right]
    rw [hsw, Perm.sign_swap hne] at hs
    exact absurd hs (by decide)
  have hB : π uLastB = uLastB := by
    rcases h (π uLastB) with hz | hz | hz
    · exact (key _ _ rfl hz).symm
    · exact absurd (π.injective (hz.trans hA.symm)) hne.symm
    · exact hz
  apply Equiv.ext
  intro x
  rw [Perm.one_apply]
  rcases h x with hx | rfl | rfl
  · exact hf x hx
  · exact hA
  · exact hB

/-- The soundness of the chain check. -/
theorem chain_sound : ∀ (ls : List ULevel) (fixed : List (Fin 24)), chainOK fixed ls = true →
    ∀ π : Perm (Fin 24), Perm.sign π = 1 → (∀ f ∈ fixed, π f = f) →
      ∃ S : List Letter, S.Sublist (ls.flatMap fun l => l.2.1) ∧ prodL S = π := by
  intro ls
  induction ls with
  | nil =>
    intro fixed hok π hs hf
    refine ⟨[], List.Sublist.refl _, ?_⟩
    have h : ∀ x : Fin 24, x ∈ fixed ∨ x = uLastA ∨ x = uLastB := by
      intro x
      simp only [chainOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
        List.contains_iff_mem, beq_iff_eq] at hok
      have := hok x
      tauto
    rw [even_last fixed h π hs hf]
    rfl
  | cons l ls ih =>
    intro fixed hok π hs hf
    simp only [chainOK, Bool.and_eq_true] at hok
    obtain ⟨hl, hrest⟩ := hok
    simp only [levelOK, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true, List.contains_iff_mem] at hl
    obtain ⟨hb, hall⟩ := hl
    have hbn : l.1 ∉ fixed := by
      intro hm
      have : fixed.contains l.1 = true := List.contains_iff_mem.2 hm
      rw [this] at hb
      exact absurd hb (by decide)
    have hxn : π l.1 ∉ fixed := by
      intro hm
      have := π.injective (hf _ hm)
      exact hbn (this ▸ hm)
    have hx := (hall (π l.1)).resolve_left hxn
    cases hlk : l.2.2.lookup (π l.1) with
    | none => rw [hlk] at hx; simp at hx
    | some T =>
      rw [hlk] at hx
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hx
      obtain ⟨⟨hT, hTb⟩, hTf⟩ := hx
      have hTinv : ∀ f ∈ fixed, (prodL T)⁻¹ f = f := by
        intro f hfm
        rw [Perm.inv_eq_iff_eq]
        exact (hTf f hfm).symm
      obtain ⟨S, hS, hSp⟩ := ih (l.1 :: fixed) hrest ((prodL T)⁻¹ * π)
        (by simp [hs, sign_prodL]) (by
          intro f hfm
          rcases List.mem_cons.1 hfm with rfl | hfm
          · simp only [Perm.mul_apply]
            rw [← hTb, perm_inv_apply]
          · simp only [Perm.mul_apply]
            rw [hf f hfm, hTinv f hfm])
      refine ⟨T ++ S, ?_, ?_⟩
      · simp only [List.flatMap_cons]
        exact hT.append hS
      · rw [prodL_append, hSp]; simp

/-- The universal sequence of letters. -/
def uSeq : List Letter := uChain.flatMap fun l => l.2.1

/-- The number of letters in the universal sequence. -/
theorem uSeq_length : uSeq.length = 275 := by decide +kernel

/-- Every even permutation of an orbit is a subproduct of the universal sequence. -/
theorem universal (π : Perm (Fin 24)) (hs : Perm.sign π = 1) :
    ∃ S : List Letter, S.Sublist uSeq ∧ prodL S = π :=
  chain_sound uChain [] uChain_ok π hs (by simp)

end RubiksGN
