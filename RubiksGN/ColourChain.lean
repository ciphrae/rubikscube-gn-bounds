import RubiksGN.ProgramGen
import RubiksGN.Lower

/-!
# Colour chains: the finite data of the coloured scheme

An orbit is coloured by `kc`. A state `σ` (the action so far on the orbit) has the right colours on a set
`F` of placed positions when `kc (σ⁻¹ f) = kc f` on `F`, and it is finished when this holds everywhere.

A family is a list of steps, in time order; it starts with nothing placed.

* A `single` step of base `b`: its entries fix the placed positions, and each unplaced position is sent to
  `b` by some entry. Exactly `4` positions have the colour of `b`, and the placed ones among them are the
  placed positions of that colour, so `w = 4 - #{f ∈ F : kc f = kc b}` entries are good.
* A `final` step: two lists on the remaining positions `Ω`. For every arrangement of the colours on `Ω`
  there is a pair of entries that puts them right.

Everything is checked by the Boolean `famCheck`, and `famChain` turns it into a `CChain`.
-/

open Equiv

namespace RubiksGN

/-! ### Colours on a set of positions -/

/-- The state has the right colours on the positions `F`. -/
def ColOK (F : List (Fin 24)) (σ : Perm (Fin 24)) : Prop := ∀ f ∈ F, kc (σ⁻¹ f) = kc f

/-- The state has the right colours everywhere. -/
def ColFull (σ : Perm (Fin 24)) : Prop := ∀ k, kc (σ⁻¹ k) = kc k

theorem ColOK.mul_fix {F : List (Fin 24)} {σ x : Perm (Fin 24)} (h : ColOK F σ)
    (hx : ∀ f ∈ F, x f = f) : ColOK F (x * σ) := by
  intro f hf
  have : x⁻¹ f = f := by
    rw [Perm.inv_eq_iff_eq]
    exact (hx f hf).symm
  rw [mul_inv_rev, Perm.mul_apply, this]
  exact h f hf

theorem card_colour (σ : Perm (Fin 24)) (c : Fin 6) :
    (Finset.univ.filter fun p => kc (σ⁻¹ p) = c).card = 4 := by
  have h1 : (Finset.univ.filter fun a => kc a = c).card = 4 :=
    (Fintype.card_of_subtype _ (by simp)).symm.trans (kc_fiber c)
  rw [← h1]
  exact Finset.card_equiv (σ⁻¹) (by simp)

/-- The number of good entries of a level of base `b`, with the positions `F` placed. -/
def wOf (F : List (Fin 24)) (b : Fin 24) : ℕ := 4 - (F.filter fun f => kc f = kc b).length

/-- **A single level.** There are at least `wOf F b` good entries. -/
theorem single_good (F : List (Fin 24)) (b : Fin 24) (l : List Tmpl) (x : Tmpl → Perm (Fin 24))
    (hfix : ∀ t ∈ l, ∀ f ∈ F, x t f = f) (hcov : ∀ p, p ∉ F → ∃ t, t ∈ l ∧ x t p = b)
    (σ : Perm (Fin 24)) (hσ : ColOK F σ) :
    ∃ G : Finset Tmpl, G ⊆ l.toFinset ∧ wOf F b ≤ G.card ∧ ∀ g ∈ G, g ∈ l ∧ ColOK (b :: F) (x g * σ) := by
  classical
  choose! τ hτ1 hτ2 using hcov
  let Pts : Finset (Fin 24) := Finset.univ.filter fun p => p ∉ F ∧ kc (σ⁻¹ p) = kc b
  have hPts : ∀ p, p ∈ Pts ↔ p ∉ F ∧ kc (σ⁻¹ p) = kc b := fun p => by simp [Pts]
  have hinj : Set.InjOn τ (Pts : Set (Fin 24)) := by
    intro p hp q hq he
    have h1 := hτ2 p ((hPts p).1 hp).1
    have h2 := hτ2 q ((hPts q).1 hq).1
    rw [he] at h1
    exact (x (τ q)).injective (h1.trans h2.symm)
  refine ⟨Pts.image τ, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    exact List.mem_toFinset.2 (hτ1 p ((hPts p).1 hp).1)
  · rw [Finset.card_image_of_injOn hinj]
    have hsub : (Finset.univ.filter fun p => kc (σ⁻¹ p) = kc b) ⊆
        Pts ∪ (F.filter fun f => kc f = kc b).toFinset := by
      intro p hp
      have hc := (Finset.mem_filter.1 hp).2
      by_cases hpF : p ∈ F
      · apply Finset.mem_union_right
        rw [List.mem_toFinset, List.mem_filter]
        refine ⟨hpF, ?_⟩
        rw [← hσ p hpF, hc]
        simp
      · exact Finset.mem_union_left _ ((hPts p).2 ⟨hpF, hc⟩)
    have h1 := Finset.card_le_card hsub
    rw [card_colour] at h1
    have h2 := Finset.card_union_le Pts (F.filter fun f => kc f = kc b).toFinset
    have h3 := List.toFinset_card_le (F.filter fun f => kc f = kc b)
    simp only [wOf]
    omega
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨hpF, hpc⟩ := (hPts p).1 hp
    have hl := hτ1 p hpF
    refine ⟨hl, ?_⟩
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · have : (x (τ p))⁻¹ f = p := by
        rw [Perm.inv_eq_iff_eq]
        exact (hτ2 p hpF).symm
      rw [mul_inv_rev, Perm.mul_apply, this]
      exact hpc
    · exact (hσ.mul_fix (hfix _ hl)) f hf

/-! ### The final levels -/

/-- The positions not yet placed. -/
def omegaOf (F : List (Fin 24)) : List (Fin 24) := (List.finRange 24).filter fun q => q ∉ F

theorem mem_omegaOf {F : List (Fin 24)} {q : Fin 24} : q ∈ omegaOf F ↔ q ∉ F := by
  simp [omegaOf]

theorem count_map_omega (F : List (Fin 24)) (f : Fin 24 → Fin 6) (a : Fin 6) :
    ((omegaOf F).map f).count a = (Finset.univ.filter fun q => q ∉ F ∧ f q = a).card := by
  have hnd : (omegaOf F).Nodup := (List.nodup_finRange 24).filter _
  rw [List.count, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext q
  simp [mem_omegaOf]

theorem card_split (F : List (Fin 24)) (f : Fin 24 → Fin 6) (a : Fin 6) :
    (Finset.univ.filter fun q => q ∉ F ∧ f q = a).card +
      (Finset.univ.filter fun q => q ∈ F ∧ f q = a).card =
      (Finset.univ.filter fun q => f q = a).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter fun q => f q = a)
    (fun q => q ∉ F)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  rw [← h]
  congr 2 <;> ext q <;> simp <;> tauto

/-- The colours on the unplaced positions are a rearrangement of the right ones. -/
theorem perm_colours {F : List (Fin 24)} {σ : Perm (Fin 24)} (hσ : ColOK F σ) :
    ((omegaOf F).map fun q => kc (σ⁻¹ q)).Perm ((omegaOf F).map kc) := by
  rw [List.perm_iff_count]
  intro a
  rw [count_map_omega, count_map_omega]
  have h1 := card_split F (fun q => kc (σ⁻¹ q)) a
  have h2 := card_split F kc a
  have h3 : (Finset.univ.filter fun q => kc q = a).card = 4 := by
    simpa using card_colour 1 a
  have h4 : (Finset.univ.filter fun q => q ∈ F ∧ kc (σ⁻¹ q) = a) =
      (Finset.univ.filter fun q => q ∈ F ∧ kc q = a) := by
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, by rw [← hσ q h, h']⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, by rw [hσ q h, h']⟩
  rw [card_colour] at h1
  rw [h4] at h1
  omega

/-- For every arrangement of the colours on the unplaced positions, a pair of entries puts it right. -/
def FinalCover (x : Tmpl → Perm (Fin 24)) (F : List (Fin 24)) (X Y : List Tmpl) : Prop :=
  ∀ c : Fin 24 → Fin 6, ((omegaOf F).map c).Perm ((omegaOf F).map kc) →
    ∃ t₁ ∈ X, ∃ t₂ ∈ Y, ∀ q ∈ omegaOf F, c ((x t₁)⁻¹ ((x t₂)⁻¹ q)) = kc q

/-- **The final levels.** -/
theorem final_good (x : Tmpl → Perm (Fin 24)) (F : List (Fin 24)) (X Y : List Tmpl)
    (hX : ∀ t ∈ X, ∀ f ∈ F, x t f = f) (hY : ∀ t ∈ Y, ∀ f ∈ F, x t f = f)
    (hc : FinalCover x F X Y) (σ : Perm (Fin 24)) (hσ : ColOK F σ) :
    ∃ t₁ ∈ X, ∃ t₂ ∈ Y, ColFull (x t₂ * (x t₁ * σ)) := by
  obtain ⟨t₁, h₁, t₂, h₂, h⟩ := hc (fun q => kc (σ⁻¹ q)) (perm_colours hσ)
  refine ⟨t₁, h₁, t₂, h₂, ?_⟩
  intro k
  by_cases hk : k ∈ F
  · exact ((hσ.mul_fix (hX _ h₁)).mul_fix (hY _ h₂)) k hk
  · have := h k (mem_omegaOf.2 hk)
    simpa [mul_inv_rev, Perm.mul_apply, _root_.mul_assoc] using this

/-! ### Boolean checks -/

/-- All ways to insert an element in a list. -/
def insertAll {α : Type*} (a : α) : List α → List (List α)
  | [] => [[a]]
  | b :: t => (a :: b :: t) :: (insertAll a t).map (b :: ·)

/-- All rearrangements of a list. Unlike `List.permutations`, this is structurally recursive, so it
reduces well in the kernel. -/
def permsL {α : Type*} : List α → List (List α)
  | [] => [[]]
  | a :: t => (permsL t).flatMap (insertAll a)

theorem mem_insertAll {α : Type*} (a : α) (p q : List α) : p ++ a :: q ∈ insertAll a (p ++ q) := by
  induction p with
  | nil => cases q <;> simp [insertAll]
  | cons b t ih =>
    simp only [List.cons_append, insertAll, List.mem_cons, List.mem_map]
    exact Or.inr ⟨_, ih, rfl⟩

theorem mem_permsL {α : Type*} (l : List α) : ∀ l' : List α, l'.Perm l → l' ∈ permsL l := by
  induction l with
  | nil =>
    intro l' h
    rw [List.perm_nil] at h
    simp [h, permsL]
  | cons a t ih =>
    intro l' h
    obtain ⟨p, q, rfl⟩ := List.append_of_mem (h.symm.subset List.mem_cons_self)
    have h2 : (p ++ q).Perm t := List.Perm.cons_inv (List.perm_middle.symm.trans h)
    simp only [permsL, List.mem_flatMap]
    exact ⟨_, ih _ h2, mem_insertAll a p q⟩

/-- The colour of a position, read off a list of colours along a list of positions. -/
def colAt : List (Fin 24) → List (Fin 6) → Fin 24 → Fin 6
  | a :: Ω, c :: cs, q => if a = q then c else colAt Ω cs q
  | _, _, _ => 0

theorem colAt_map (c : Fin 24 → Fin 6) : ∀ (Ω : List (Fin 24)) (q : Fin 24), q ∈ Ω →
    colAt Ω (Ω.map c) q = c q := by
  intro Ω
  induction Ω with
  | nil => simp
  | cons a t ih =>
    intro q hq
    simp only [List.map_cons, colAt]
    by_cases h : a = q
    · rw [if_pos h, h]
    · rw [if_neg h]
      exact ih q ((List.mem_cons.1 hq).resolve_left (Ne.symm h))

/-- The Boolean form of `FinalCover`. -/
def finalCheck (x : Tmpl → Perm (Fin 24)) (F : List (Fin 24)) (X Y : List Tmpl) : Bool :=
  (permsL ((omegaOf F).map kc)).all fun cs =>
    X.any fun t₁ => Y.any fun t₂ =>
      (omegaOf F).all fun q => colAt (omegaOf F) cs ((x t₁)⁻¹ ((x t₂)⁻¹ q)) == kc q

theorem finalCheck_sound (x : Tmpl → Perm (Fin 24)) (F : List (Fin 24)) (X Y : List Tmpl)
    (hX : ∀ t ∈ X, ∀ f ∈ F, x t f = f) (hY : ∀ t ∈ Y, ∀ f ∈ F, x t f = f)
    (h : finalCheck x F X Y = true) : FinalCover x F X Y := by
  intro c hc
  simp only [finalCheck, List.all_eq_true] at h
  have h1 := h _ (mem_permsL _ _ hc)
  simp only [List.any_eq_true, List.all_eq_true, beq_iff_eq] at h1
  obtain ⟨t₁, ht₁, t₂, ht₂, h2⟩ := h1
  refine ⟨t₁, ht₁, t₂, ht₂, fun q hq => ?_⟩
  rw [← h2 q hq, colAt_map]
  rw [mem_omegaOf]
  intro hmem
  have hq' := mem_omegaOf.1 hq
  apply hq'
  have e1 : x t₂ ((x t₁) ((x t₁)⁻¹ ((x t₂)⁻¹ q))) = q := by simp
  rw [hX t₁ ht₁ _ hmem, hY t₂ ht₂ _ hmem] at e1
  exact e1 ▸ hmem

/-! ### Steps -/

/-- A step of a family. `kT` tells whether it places positions of the target orbit (`true`) or of the
mirror orbit (`false`). -/
inductive ColStep
  | single (kT : Bool) (b : Fin 24) (l : List Tmpl)
  | final (kT : Bool) (X Y : List Tmpl)

/-- The element of an entry on the target or the mirror orbit. -/
def xK (d kT : Bool) (t : Tmpl) : Perm (Fin 24) := if kT then xT d t else xM d t

/-- The placed positions on the target and on the mirror orbit. -/
abbrev Placed := List (Fin 24) × List (Fin 24)

/-- The positions placed on the orbit of a kind. -/
def Placed.of (kT : Bool) (p : Placed) : List (Fin 24) := if kT then p.1 else p.2

/-- The placed positions after a step. -/
def ColStep.next : ColStep → Placed → Placed
  | .single kT b _, p => if kT then (b :: p.1, p.2) else (p.1, b :: p.2)
  | .final kT _ _, p => if kT then (List.finRange 24, p.2) else (p.1, List.finRange 24)

/-- The entries of a list fix the placed positions, on both orbits. -/
def fixesAll (d : Bool) (p : Placed) (l : List Tmpl) : Bool :=
  l.all fun t => p.1.all (fun f => xT d t f == f) && p.2.all (fun f => xM d t f == f)

theorem fixesAll_spec {d : Bool} {p : Placed} {l : List Tmpl} (h : fixesAll d p l = true) :
    ∀ t ∈ l, (∀ f ∈ p.1, xT d t f = f) ∧ (∀ f ∈ p.2, xM d t f = f) := by
  intro t ht
  simp only [fixesAll, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h t ht

/-- The check of a step. -/
def ColStep.check (d : Bool) : ColStep → Placed → Bool
  | .single kT b l, p =>
    fixesAll d p l && (List.finRange 24).all fun q =>
      (p.of kT).contains q || l.any fun t => xK d kT t q == b
  | .final kT X Y, p =>
    fixesAll d p X && fixesAll d p Y && finalCheck (xK d kT) (p.of kT) X Y

/-- The check of a family: all its steps are right, and at the end all positions are placed. -/
def famCheck (d : Bool) : List ColStep → Placed → Bool
  | [], p => (List.finRange 24).all fun k => p.1.contains k && p.2.contains k
  | st :: t, p => st.check d p && famCheck d t (st.next p)

/-- The levels of a family. -/
def famLevels : List ColStep → Placed → List CLevel
  | [], _ => []
  | .single kT b l :: t, p => ⟨l, wOf (p.of kT) b⟩ :: famLevels t ((ColStep.single kT b l).next p)
  | .final kT X Y :: t, p =>
    ⟨X, 1⟩ :: ⟨Y, 1⟩ :: famLevels t ((ColStep.final kT X Y).next p)

/-- The invariant of a set of placed positions. -/
def ColInv (p : Placed) (s : CState) : Prop := ColOK p.1 s.1 ∧ ColOK p.2 s.2

/-- The final invariant. -/
def ColGoal (s : CState) : Prop := ColFull s.1 ∧ ColFull s.2

theorem colOK_finRange {σ : Perm (Fin 24)} (h : ColFull σ) : ColOK (List.finRange 24) σ :=
  fun f _ => h f

/-- **A family's check gives a chain**, from the invariant at `p` to the final invariant. -/
theorem famChain (d : Bool) : ∀ (steps : List ColStep) (p : Placed), famCheck d steps p = true →
    CChain d (famLevels steps p) (ColInv p) ColGoal := by
  intro steps
  induction steps with
  | nil =>
    intro p h s hs
    simp only [famCheck, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨fun k => hs.1 k (h k (List.mem_finRange k)).1,
      fun k => hs.2 k (h k (List.mem_finRange k)).2⟩
  | cons st t ih =>
    intro p h
    simp only [famCheck, Bool.and_eq_true] at h
    obtain ⟨hst, ht⟩ := h
    have hrest := ih _ ht
    cases st with
    | single kT b l =>
      simp only [ColStep.check, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        List.contains_iff_mem, List.any_eq_true, beq_iff_eq] at hst
      obtain ⟨hfix, hcov⟩ := hst
      have hfix' := fixesAll_spec hfix
      refine ⟨ColInv ((ColStep.single kT b l).next p), ?_, hrest⟩
      intro s hs
      cases kT with
      | true =>
        obtain ⟨G, g1, g2, g3⟩ := single_good p.1 b l (xT d) (fun u hu => (hfix' u hu).1)
          (fun q hq => by
            have := (hcov q (List.mem_finRange q)).resolve_left hq
            simpa [xK] using this)
          s.1 hs.1
        refine ⟨G, g1, g2, fun g hg => ?_⟩
        obtain ⟨g4, g5⟩ := g3 g hg
        exact ⟨g5, hs.2.mul_fix (hfix' g g4).2⟩
      | false =>
        obtain ⟨G, g1, g2, g3⟩ := single_good p.2 b l (xM d) (fun u hu => (hfix' u hu).2)
          (fun q hq => by
            have := (hcov q (List.mem_finRange q)).resolve_left hq
            simpa [xK] using this)
          s.2 hs.2
        refine ⟨G, g1, g2, fun g hg => ?_⟩
        obtain ⟨g4, g5⟩ := g3 g hg
        exact ⟨hs.1.mul_fix (hfix' g g4).1, g5⟩
    | final kT X Y =>
      simp only [ColStep.check, Bool.and_eq_true] at hst
      obtain ⟨⟨hfX, hfY⟩, hfc⟩ := hst
      have hfX' := fixesAll_spec hfX
      have hfY' := fixesAll_spec hfY
      refine ⟨fun s => ∃ y ∈ Y, ColInv ((ColStep.final kT X Y).next p) (stepS d y s), ?_,
        ColInv ((ColStep.final kT X Y).next p), ?_, hrest⟩
      · intro s hs
        cases kT with
        | true =>
          have hc := finalCheck_sound (xK d true) p.1 X Y (fun u hu => (hfX' u hu).1)
            (fun u hu => (hfY' u hu).1) hfc
          obtain ⟨t₁, h₁, t₂, h₂, hf⟩ := final_good (xK d true) p.1 X Y (fun u hu => (hfX' u hu).1)
            (fun u hu => (hfY' u hu).1) hc s.1 hs.1
          refine ⟨{t₁}, by simpa using h₁, by simp, fun g hg => ?_⟩
          rw [Finset.mem_singleton.1 hg]
          refine ⟨t₂, h₂, colOK_finRange hf, ?_⟩
          exact (hs.2.mul_fix (hfX' t₁ h₁).2).mul_fix (hfY' t₂ h₂).2
        | false =>
          have hc := finalCheck_sound (xK d false) p.2 X Y (fun u hu => (hfX' u hu).2)
            (fun u hu => (hfY' u hu).2) hfc
          obtain ⟨t₁, h₁, t₂, h₂, hf⟩ := final_good (xK d false) p.2 X Y (fun u hu => (hfX' u hu).2)
            (fun u hu => (hfY' u hu).2) hc s.2 hs.2
          refine ⟨{t₁}, by simpa using h₁, by simp, fun g hg => ?_⟩
          rw [Finset.mem_singleton.1 hg]
          refine ⟨t₂, h₂, ?_, colOK_finRange hf⟩
          exact (hs.1.mul_fix (hfX' t₁ h₁).1).mul_fix (hfY' t₂ h₂).1
      · rintro s ⟨y, hy, hys⟩
        exact ⟨{y}, by simpa using hy, by simp, fun g hg => by
          rw [Finset.mem_singleton.1 hg]; exact hys⟩

end RubiksGN
