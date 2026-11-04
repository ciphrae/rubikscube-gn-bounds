import RubiksGN.SkelCheck

/-!
# From a passing chain check to short words

If `chainCheck` passes then the value of any word with even layer counts lies in the group of the
chain, and is the value of a short word of the chain.
-/

open Equiv

namespace RubiksGN

theorem mem_allSyms : ∀ s : Sym, s ∈ allSyms := by decide

/-- The value of a letter on a piece: trivial unless its layer is classified. -/
def Fp {N : ℕ} {ι : Type*} (cls : ι → Option (Fin 3)) (sp : Sym → Perm (Fin N))
    (l : Axis × ι × Bool) : Perm (Fin N) :=
  match cls l.2.1 with
  | none => 1
  | some c => sp (l.1, c, l.2.2)

section

variable {N : ℕ} (hN : N ≤ 32) {sp : Sym → Perm (Fin N)} {tab : List Tb} {ls : List Level}
  (hs : ∀ s, Rep (sp s) (tableOf tab s)) (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹)
  (hchk : chainCheck N tab ls = true)

include hN hs hflip hchk

theorem chk_entries : ∀ e ∈ gensOf ls, entryOK N (tableOf tab) e = true := by
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true] at hchk
  exact hchk.1.1.1

theorem chk_closed : InP sp ls 1 ∧ ∀ s ∈ gensOf ls, ∀ g, InP sp ls g → InP sp ls (evalS sp s.w * g) := by
  have hE := chk_entries hN hs hflip hchk
  simp only [chainCheck, Bool.and_eq_true] at hchk
  exact closed_sound hN hs hflip ls hE hchk.1.1.2

theorem chk_mem {g : Perm (Fin N)} {t : Tb} (hg : Rep g t) (h : inP N ls t = true) :
    g ∈ groupOf sp ls :=
  InP_mem ls ls (fun _ hx => hx) g
    (inP_sound hN hs hflip ls (chk_entries hN hs hflip hchk) g t hg h)

theorem chk_same (s s' : Sym) (hk : Sym.sameKey s s' = true) : sp s * sp s' ∈ groupOf sp ls := by
  have h := hchk
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.1.2 s (mem_allSyms s) s' (mem_allSyms s')).1
  simp only [hk, Bool.not_true, Bool.false_or] at this
  exact chk_mem hN hs hflip hchk ((hs s).mul (hs s')) this

theorem chk_comm (s s' : Sym) : sp s * sp s' * (sp s)⁻¹ * (sp s')⁻¹ ∈ groupOf sp ls := by
  have h := hchk
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.1.2 s (mem_allSyms s) s' (mem_allSyms s')).2
  have hr := (((hs s).mul (hs s')).mul (hs s.flip)).mul (hs s'.flip)
  rw [hflip, hflip] at hr
  exact chk_mem hN hs hflip hchk hr this

theorem chk_conj (s : Sym) (k : Perm (Fin N)) (hk : k ∈ groupOf sp ls) :
    sp s * k * (sp s)⁻¹ ∈ groupOf sp ls := by
  have hE := chk_entries hN hs hflip hchk
  have h := hchk
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true] at h
  induction hk using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, rfl⟩ := hy
    have := h.2 s (mem_allSyms s) e he
    have hr := ((hs s).mul (entry_rep hN hs (hE e he))).mul (hs s.flip)
    rw [hflip] at hr
    exact chk_mem hN hs hflip hchk hr this
  | one => simp
  | mul y z _ _ iy iz =>
    have := mul_mem iy iz
    convert this using 1
    group
  | inv y _ iy =>
    have := inv_mem iy
    convert this using 1
    group

/-- A word with even layer counts lands in the group of the chain. -/
theorem even_mem {ι : Type*} [DecidableEq ι] (cls : ι → Option (Fin 3)) (w : List (Axis × ι × Bool))
    (he : ∀ c : Axis × ι, Even ((w.map fun l => (l.1, l.2.1)).count c)) :
    (w.map (Fp cls sp)).prod ∈ groupOf sp ls := by
  refine even_word_mem (Fp cls sp) (fun l => (l.1, l.2.1)) (groupOf sp ls) ?_ ?_ ?_ ?_ _ w rfl he
  · rintro ⟨a, i, d⟩ ⟨a', i', d'⟩ hk
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [Fp]
    cases cls i with
    | none => simp [one_mem]
    | some c =>
      exact chk_same hN hs hflip hchk _ _ (by simp [Sym.sameKey])
  · rintro ⟨a, i, d⟩ ⟨a', i', d'⟩
    simp only [Fp]
    cases cls i <;> cases cls i' <;> simp [one_mem]
    exact chk_comm hN hs hflip hchk _ _
  · rintro ⟨a, i, d⟩ k hk
    simp only [Fp]
    cases cls i with
    | none => simpa using hk
    | some c => exact chk_conj hN hs hflip hchk _ k hk
  · rintro ⟨a, i, d⟩
    refine ⟨(a, i, !d), ?_, rfl⟩
    simp only [Fp]
    cases cls i with
    | none => simp
    | some c => exact hflip (a, c, d)

end

theorem length_le_foldr (e : Entry) (es : List Entry) (h : e ∈ es) :
    e.w.length ≤ (es.map fun e => e.w.length).foldr max 0 := by
  induction es with
  | nil => simp at h
  | cons x t ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

/-- A property of words preserved under concatenation and true of all chain words holds of some
short word for every product of the chain. -/
theorem word_of_InP {N : ℕ} {sp : Sym → Perm (Fin N)} (Q : List Sym → Prop) (hQ0 : Q [])
    (hQa : ∀ u v, Q u → Q v → Q (u ++ v)) :
    ∀ (ls : List Level), (∀ e ∈ gensOf ls, Q e.w) → ∀ g, InP sp ls g →
      ∃ w, evalS sp w = g ∧ w.length ≤ boundOf ls ∧ Q w := by
  intro ls
  induction ls with
  | nil =>
    intro _ g hg
    simp only [InP] at hg
    subst hg
    exact ⟨[], rfl, by simp, hQ0⟩
  | cons l ls ih =>
    rintro hq g ⟨e, he, h, hh, rfl⟩
    obtain ⟨w, hw, hlen, hQw⟩ := ih (fun x hx => hq x (by
      simp only [gensOf, List.flatMap_cons]; exact List.mem_append_right _ hx)) h hh
    refine ⟨e.w ++ w, ?_, ?_, hQa _ _ (hq e (by
      simp only [gensOf, List.flatMap_cons]; exact List.mem_append_left _ he)) hQw⟩
    · simp [evalS] at hw ⊢
      rw [hw]
    · simp only [List.length_append, boundOf, List.map_cons, List.sum_cons] at hlen ⊢
      exact Nat.add_le_add (length_le_foldr e l.es he) hlen

end RubiksGN
