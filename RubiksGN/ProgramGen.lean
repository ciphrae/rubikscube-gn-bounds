import RubiksGN.Program
import RubiksGN.ColouredCost
import RubiksGN.Covering

/-!
# Programs with separate families, and the choice of values by covering

A *family* is one half of a block (`QO` with `d = true`, `QE` with `d = false`). All its data is written
in **time order**: `x₁` is applied first, and the program acts by `x_N ⋯ x₁`. An entry `t` acts on the
target orbit by `xT d t` and on the mirror orbit by `xM d t`, where `d = true` means `eT t`, `eM t` and
`d = false` means `(eT t)⁻¹`, `(eM t)⁻¹`.

* `program_gen`: two lists of jobs, in time order, zipped into rounds.
* `CChain`: an abstract chain of levels: at a state satisfying the invariant at least `w` entries of the
  level's list lead to a state satisfying the next invariant.
* `exists_family`: the value selection: from a chain, jobs with a small number of patterns per chunk, by
  the covering lemma, such that every pair of the family ends in the final invariant.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### The action of a family -/

/-- The time-order element of an entry on the target orbit. -/
def xT (d : Bool) (t : Tmpl) : Perm (Fin 24) := if d then eT t else (eT t)⁻¹

/-- The time-order element of an entry on the mirror orbit. -/
def xM (d : Bool) (t : Tmpl) : Perm (Fin 24) := if d then eM t else (eM t)⁻¹

/-- The action of jobs in time order: the first job is applied first. -/
def famAct (L : ℕ) (F : Tmpl → Perm (Fin 24)) (js : List (Job n)) (i j : Fin n) : Perm (Fin 24) :=
  (js.reverse.map fun J => if i ∈ J.X then F (clampT L (J.pat j i)) else 1).prod

theorem famAct_nil (L : ℕ) (F : Tmpl → Perm (Fin 24)) (i j : Fin n) :
    famAct L F ([] : List (Job n)) i j = 1 := rfl

theorem famAct_append (L : ℕ) (F : Tmpl → Perm (Fin 24)) (a b : List (Job n)) (i j : Fin n) :
    famAct L F (a ++ b) i j = famAct L F b i j * famAct L F a i j := by
  simp [famAct, List.reverse_append, List.map_append, List.prod_append]

/-! ### A program -/

/-- **A program with separate families.** The jobs of `QO` and `QE` are given in time order. -/
theorem program_gen (hn : 2 ≤ n) {QO QE Y : Finset (Fin n)} (c : PairCtx (QO ∪ QE) Y)
    (hd : Disjoint QO QE) (L Cslot R : ℕ) (jsO jsE : List (Job n)) (hRO : jsO.length ≤ R)
    (hRE : jsE.length ≤ R) (hO : ∀ J ∈ jsO, J.X ⊆ QO ∧ J.cost L Y ≤ Cslot)
    (hE : ∀ J ∈ jsE, J.X ⊆ QE ∧ J.cost L Y ≤ Cslot) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧ W.length ≤ R * (2 * Y.card + 2 * Cslot) ∧ FixesSkel hn W ∧
      ∀ i j, IsRow i → IsCol j →
        Rv (rep i j) W =
          if i ∈ QO ∧ j ∈ Y then famAct L (xT true) jsO i j
          else if i ∈ QE ∧ j ∈ Y then famAct L (xT false) jsE i j
          else if Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y then famAct L (xM true) jsO (Fin.rev j) (Fin.rev i)
          else if Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y then famAct L (xM false) jsE (Fin.rev j) (Fin.rev i)
          else 1 := by
  have hOU : QO ⊆ QO ∪ QE := Finset.subset_union_left
  have hEU : QE ⊆ QO ∪ QE := Finset.subset_union_right
  obtain ⟨W, w1, w2, w3, w4⟩ := exists_rounds hn c hOU hEU hd L Cslot R jsO.reverse jsE.reverse
    (by simpa using hRO) (by simpa using hRE)
    (fun J hJ => hO J (List.mem_reverse.1 hJ)) (fun J hJ => hE J (List.mem_reverse.1 hJ))
  refine ⟨W, w1, w2, w3, ?_⟩
  intro i j hi hj
  obtain ⟨A1, A2⟩ := w4 i j hi hj
  have offO : ∀ J ∈ jsO.reverse, ¬ (i ∈ QO ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(hO J (List.mem_reverse.1 hJ)).1 h.1, h.2⟩)
    (fun h => h₂ ⟨(hO J (List.mem_reverse.1 hJ)).1 h.1, h.2⟩)
  have offE : ∀ J ∈ jsE.reverse, ¬ (i ∈ QE ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(hE J (List.mem_reverse.1 hJ)).1 h.1, h.2⟩)
    (fun h => h₂ ⟨(hE J (List.mem_reverse.1 hJ)).1 h.1, h.2⟩)
  by_cases c1 : i ∈ QO ∧ j ∈ Y
  · have hnE : ¬ (i ∈ QE ∧ j ∈ Y) := fun h => Finset.disjoint_left.1 hd c1.1 h.1
    have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c1.2 (hEU h.1)
    rw [if_pos c1, A1 (fun J hJ => offE J hJ hnE hnE'), famAct]
    congr 1
    refine List.map_congr_left fun J hJ => ?_
    rw [Job.act_target c L (((hO J (List.mem_reverse.1 hJ)).1).trans hOU) c1.2]
    rfl
  · rw [if_neg c1]
    by_cases c2 : i ∈ QE ∧ j ∈ Y
    · have hnO' : ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c2.2 (hOU h.1)
      rw [if_pos c2, A2 (fun J hJ => offO J hJ c1 hnO'), famAct]
      congr 1
      refine List.map_congr_left fun J hJ => ?_
      rw [Job.act_target c L (((hE J (List.mem_reverse.1 hJ)).1).trans hEU) c2.2]
      by_cases h : i ∈ J.X
      · simp [h, xT]
      · simp [h]
    · rw [if_neg c2]
      by_cases c3 : Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y
      · have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) :=
          fun h => Finset.disjoint_left.1 hd c3.1 h.1
        rw [if_pos c3, A1 (fun J hJ => offE J hJ c2 hnE'), famAct]
        congr 1
        refine List.map_congr_left fun J hJ => ?_
        rw [Job.act_mirror c L (((hO J (List.mem_reverse.1 hJ)).1).trans hOU) c3.2]
        rfl
      · rw [if_neg c3]
        by_cases c4 : Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y
        · rw [if_pos c4, A2 (fun J hJ => offO J hJ c1 c3), famAct]
          congr 1
          refine List.map_congr_left fun J hJ => ?_
          rw [Job.act_mirror c L (((hE J (List.mem_reverse.1 hJ)).1).trans hEU) c4.2]
          by_cases h : Fin.rev j ∈ J.X
          · simp [h, xM]
          · simp [h]
        · rw [if_neg c4, A1 (fun J hJ => offE J hJ c2 c4)]
          apply List.prod_eq_one
          intro x hx
          obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
          exact offO J hJ c1 c3

/-! ### Chains -/

/-- The state of a pair: the action so far on the target orbit and on the mirror orbit. -/
abbrev CState := Perm (Fin 24) × Perm (Fin 24)

/-- One entry applied to a state. -/
def stepS (d : Bool) (t : Tmpl) (s : CState) : CState := (xT d t * s.1, xM d t * s.2)

/-- A level: a list of entries, and a lower bound on the number of good entries. -/
structure CLevel where
  l : List Tmpl
  w : ℕ

/-- The key of a level: the size of its list and the number of good entries. -/
def CLevel.key (v : CLevel) : ℕ × ℕ := (v.l.length, v.w)

/-- A chain of levels, from the invariant `P` to the invariant `Q`. -/
def CChain (d : Bool) : List CLevel → (CState → Prop) → (CState → Prop) → Prop
  | [], P, Q => ∀ s, P s → Q s
  | v :: t, P, Q => ∃ P' : CState → Prop,
      (∀ s, P s → ∃ G : Finset Tmpl, G ⊆ v.l.toFinset ∧ v.w ≤ G.card ∧ ∀ g ∈ G, P' (stepS d g s)) ∧
        CChain d t P' Q

/-! ### Choosing the values of one level -/

/-- **One level.** A single function of values is chosen on all chunks; it has few patterns on each
chunk, and it picks a good value for each pair. -/
theorem exists_level_pat {R Y : Finset (Fin n)} {chunks : List (Finset (Fin n))} {sz : ℕ}
    (hch : IsChunking R sz chunks) (A : Finset Tmpl) (G : Fin n → Fin n → Finset Tmpl)
    (m w N T : ℕ) (hw : 0 < w) (hwm : w ≤ m) (hA : A.card ≤ m) (hY : Y.card ≤ N)
    (hT : ((m : ℝ) / w) ^ sz * (Real.log (N : ℝ) + 1) + 1 ≤ T)
    (hGA : ∀ i ∈ R, ∀ j ∈ Y, G i j ⊆ A) (hGw : ∀ i ∈ R, ∀ j ∈ Y, w ≤ (G i j).card) :
    ∃ pat : Fin n → Fin n → Tmpl, (∀ i ∈ R, ∀ j ∈ Y, pat j i ∈ G i j) ∧
      ∀ X ∈ chunks, (patsOf X Y pat).card ≤ T := by
  classical
  have hcov : ∀ X ∈ chunks, ∃ C : Finset (X → Tmpl), C.card ≤ T ∧
      ∀ j ∈ Y, ∃ p ∈ C, ∀ i : X, p i ∈ G i.1 j := by
    intro X hX
    have hsub := hch.sub X hX
    obtain ⟨C, hC, hcover⟩ := covering (ι := X) A Y (fun i j => G i.1 j) m w sz N hw hwm hA
      (by simpa using hch.card X hX) hY (fun i j hj => hGA i.1 (hsub i.2) j hj)
      (fun i j hj => hGw i.1 (hsub i.2) j hj)
    exact ⟨C, by exact_mod_cast hC.trans hT, hcover⟩
  choose! C hC hcover using hcov
  have hchunk : ∀ i : Fin n, ∃ X : Finset (Fin n), i ∈ R → (X ∈ chunks ∧ i ∈ X) := by
    intro i
    by_cases hi : i ∈ R
    · obtain ⟨X, hX, hiX⟩ := hch.cover i hi
      exact ⟨X, fun _ => ⟨hX, hiX⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose chunkOf hchunkOf using hchunk
  have huniq : ∀ X ∈ chunks, ∀ i ∈ X, chunkOf i = X := by
    intro X hX i hi
    obtain ⟨h1, h2⟩ := hchunkOf i (hch.sub X hX hi)
    by_contra hne
    have hdis : Disjoint (chunkOf i) X :=
      hch.disj.forall h1 hX hne
    exact Finset.disjoint_left.1 hdis h2 hi
  -- a pattern for each chunk and each column
  have hp : ∀ (X : Finset (Fin n)) (j : Fin n), ∃ p : X → Tmpl, X ∈ chunks → j ∈ Y →
      p ∈ C X ∧ ∀ i : X, p i ∈ G i.1 j := by
    intro X j
    by_cases h : X ∈ chunks ∧ j ∈ Y
    · obtain ⟨p, hp1, hp2⟩ := hcover X h.1 j h.2
      exact ⟨p, fun _ _ => ⟨hp1, hp2⟩⟩
    · exact ⟨fun _ => [], fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose q hq using hp
  let pat : Fin n → Fin n → Tmpl := fun j i =>
    if h : i ∈ chunkOf i then q (chunkOf i) j ⟨i, h⟩ else []
  have hpat : ∀ X ∈ chunks, ∀ (i : Fin n) (hi : i ∈ X) (j : Fin n), pat j i = q X j ⟨i, hi⟩ := by
    intro X hX i hi j
    have he := huniq X hX i hi
    subst he
    exact dif_pos hi
  refine ⟨pat, ?_, ?_⟩
  · intro i hi j hj
    obtain ⟨h1, h2⟩ := hchunkOf i hi
    rw [hpat _ h1 i h2 j]
    exact (hq _ j h1 hj).2 ⟨i, h2⟩
  · intro X hX
    refine (Finset.card_le_card ?_).trans (hC X hX)
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    have : patOf X pat j = q X j := by
      funext i
      exact hpat X hX i.1 i.2 j
    rw [this]
    exact (hq X j hX hj).1

/-- The jobs of a level act by the value of the pair. -/
theorem famAct_level {R : Finset (Fin n)} {chunks : List (Finset (Fin n))} {sz : ℕ}
    (hch : IsChunking R sz chunks) (L : ℕ) (F : Tmpl → Perm (Fin 24)) (pat : Fin n → Fin n → Tmpl)
    {i : Fin n} (hi : i ∈ R) (j : Fin n) :
    famAct L F (chunks.map fun X => (⟨X, pat⟩ : Job n)) i j = F (clampT L (pat j i)) := by
  have hd : chunks.reverse.Pairwise Disjoint :=
    List.pairwise_reverse.2 (hch.disj.imp fun h => Disjoint.symm h)
  obtain ⟨X, hX, hiX⟩ := hch.cover i hi
  have h := chunk_prod (F (clampT L (pat j i))) chunks.reverse hd
    (i := i) ⟨X, List.mem_reverse.2 hX, hiX⟩
  rw [← h, famAct, ← List.map_reverse, List.map_map]
  rfl

/-! ### The value selection -/

/-- The requirements on one level of a family. -/
structure LevelOK (L Cslot N : ℕ) (sOf Tb : ℕ × ℕ → ℕ) (v : CLevel) : Prop where
  w_pos : 0 < v.w
  w_le : v.w ≤ v.l.length
  s_pos : 0 < sOf v.key
  len : ∀ t ∈ v.l, tmplLen t ≤ L
  tb : ((v.l.length : ℝ) / v.w) ^ sOf v.key * (Real.log (N : ℝ) + 1) + 1 ≤ Tb v.key
  slot : Tb v.key * (2 * sOf v.key * L) ≤ Cslot

/-- **The value selection.** From a chain, jobs in time order such that every pair of the family ends in
the final invariant, with a number of patterns per chunk given by the covering lemma. -/
theorem exists_family {R Y : Finset (Fin n)} (d : Bool) (L Cslot N : ℕ) (sOf Tb : ℕ × ℕ → ℕ)
    (hY : Y.card ≤ N) :
    ∀ (lv : List CLevel) (P Q : CState → Prop) (s : Fin n → Fin n → CState),
      (∀ v ∈ lv, LevelOK L Cslot N sOf Tb v) → CChain d lv P Q → (∀ i ∈ R, ∀ j ∈ Y, P (s i j)) →
      ∃ js : List (Job n), js.length ≤ (lv.map fun v => R.card / sOf v.key + 1).sum ∧
        (∀ J ∈ js, J.X ⊆ R ∧ J.cost L Y ≤ Cslot) ∧
        ∀ i ∈ R, ∀ j ∈ Y,
          Q (famAct L (xT d) js i j * (s i j).1, famAct L (xM d) js i j * (s i j).2) := by
  classical
  intro lv
  induction lv with
  | nil =>
    intro P Q s _ hc hs
    refine ⟨[], by simp, by simp, ?_⟩
    intro i hi j hj
    simp only [famAct_nil, one_mul]
    exact hc _ (hs i hi j hj)
  | cons v t ih =>
    intro P Q s hok hc hs
    obtain ⟨P', hstep, htail⟩ := hc
    have hv := hok v List.mem_cons_self
    have hG : ∀ i j : Fin n, ∃ G : Finset Tmpl, i ∈ R → j ∈ Y → G ⊆ v.l.toFinset ∧ v.w ≤ G.card ∧
        ∀ g ∈ G, P' (stepS d g (s i j)) := by
      intro i j
      by_cases h : i ∈ R ∧ j ∈ Y
      · obtain ⟨G, g1, g2, g3⟩ := hstep _ (hs i h.1 j h.2)
        exact ⟨G, fun _ _ => ⟨g1, g2, g3⟩⟩
      · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
    choose G hG using hG
    obtain ⟨chunks, hch⟩ := exists_chunking (sOf v.key) hv.s_pos R
    obtain ⟨pat, hpat, hcard⟩ := exists_level_pat hch v.l.toFinset G v.l.length v.w N (Tb v.key)
      hv.w_pos hv.w_le (List.toFinset_card_le _) hY hv.tb
      (fun i hi j hj => (hG i j hi hj).1) (fun i hi j hj => (hG i j hi hj).2.1)
    have hmem : ∀ i ∈ R, ∀ j ∈ Y, pat j i ∈ v.l := fun i hi j hj =>
      List.mem_toFinset.1 ((hG i j hi hj).1 (hpat i hi j hj))
    obtain ⟨js, h1, h2, h3⟩ := ih P' Q (fun i j => stepS d (pat j i) (s i j))
      (fun w hw => hok w (List.mem_cons_of_mem _ hw)) htail
      (fun i hi j hj => (hG i j hi hj).2.2 _ (hpat i hi j hj))
    refine ⟨chunks.map (fun X => (⟨X, pat⟩ : Job n)) ++ js, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.map_cons, List.sum_cons]
      have := hch.length
      omega
    · intro J hJ
      rcases List.mem_append.1 hJ with h | h
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
        refine ⟨hch.sub X hX, ?_⟩
        calc Job.cost L Y ⟨X, pat⟩ = (patsOf X Y pat).card * (2 * X.card * L) := rfl
          _ ≤ Tb v.key * (2 * sOf v.key * L) :=
            Nat.mul_le_mul (hcard X hX)
              (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hch.card X hX)))
          _ ≤ Cslot := hv.slot
      · exact h2 J h
    · intro i hi j hj
      have hclamp : clampT L (pat j i) = pat j i := clampT_of_le (hv.len _ (hmem i hi j hj))
      have h4 := h3 i hi j hj
      simp only [stepS] at h4
      rw [famAct_append, famAct_append, famAct_level hch L _ pat hi j, famAct_level hch L _ pat hi j,
        hclamp, _root_.mul_assoc, _root_.mul_assoc]
      exact h4

/-- The number of jobs of a family of at most `S / 2` rows. -/
theorem family_length_le (A S : ℕ) (hA : A ≤ S / 2) (sOf : ℕ × ℕ → ℕ) (lv : List CLevel) :
    (lv.map fun v => A / sOf v.key + 1).sum ≤ colRounds S sOf (lv.map CLevel.key) := by
  induction lv with
  | nil => simp [colRounds]
  | cons v t ih =>
    simp only [colRounds, List.map_cons, List.sum_cons] at ih ⊢
    have := Nat.div_le_div_right (c := sOf v.key) hA
    omega

end RubiksGN
