import RubiksGN.Trie
import RubiksGN.SolveExact

/-!
# Programs and the solver with trie slots

The rounds, jobs, programs and the solver of `RubiksGN/Program.lean` and `RubiksGN/SolveExact.lean`, with the passes written as tries:
the action is the same (`trieW_Rv`), and the cost is that of `trieExactW`.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### Rounds -/

/-- The edges of a job. -/
noncomputable def Job.edges (L : ℕ) (Y : Finset (Fin n)) (J : Job n) : ℕ :=
  passEdges J.X Y (clampT L) J.pat

theorem Job.emp_edges (L : ℕ) (Y : Finset (Fin n)) : (Job.emp : Job n).edges L Y = 0 := by
  simp [Job.edges, passEdges, Job.emp, trieCost]

/-- The round of two jobs, with tries. -/
noncomputable def jobRoundT (hn : 2 ≤ n) (L : ℕ) (Y : Finset (Fin n)) (J₁ J₂ : Job n) : Word n :=
  trieW hn J₁.X Y (clampT L) J₁.pat true ++ trieW hn J₂.X Y (clampT L) J₂.pat false

theorem jobRoundT_Rv (hn : 2 ≤ n) {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (L : ℕ) {J₁ J₂ : Job n}
    (h₁ : J₁.X ⊆ Q) (h₂ : J₂.X ⊆ Q) (hd : Disjoint J₁.X J₂.X) {i j : Fin n} (hi : IsRow i)
    (hj : IsCol j) :
    Rv (rep i j) (jobRoundT hn L Y J₁ J₂) = J₁.act L Y i j * (J₂.act L Y i j)⁻¹ := by
  rw [← jobRound_Rv hn c L h₁ h₂ hd hi hj, jobRoundT, jobRound, roundW, Rv_append, Rv_append,
    trieW_Rv hn (c.mono h₁) _ _ _ hi hj, trieW_Rv hn (c.mono h₂) _ _ _ hi hj]

theorem jobRoundT_length (hn : 2 ≤ n) (L : ℕ) (Y : Finset (Fin n)) (J₁ J₂ : Job n) :
    (jobRoundT hn L Y J₁ J₂).length = 2 * Y.card + (J₁.edges L Y + J₂.edges L Y) := by
  simp only [jobRoundT, List.length_append, trieW_length, Job.edges]
  ring

theorem jobRoundT_isQ (hn : 2 ≤ n) (L : ℕ) (Y : Finset (Fin n)) (J₁ J₂ : Job n) :
    ∀ m ∈ jobRoundT hn L Y J₁ J₂, IsQ m := by
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact trieW_isQ hn _ _ _ _ _ m h
  · exact trieW_isQ hn _ _ _ _ _ m h

theorem jobRoundT_fixesSkel (hn : 2 ≤ n) {Y : Finset (Fin n)}
    (hY : ∀ j ∈ Y, 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1) (L : ℕ) (J₁ J₂ : Job n) :
    FixesSkel hn (jobRoundT hn L Y J₁ J₂) :=
  (trieW_fixesSkel hn hY _ _ _).append (trieW_fixesSkel hn hY _ _ _)

theorem sum_head_tail {β : Type*} (f : β → ℕ) (e : β) (he : f e = 0) (a : List β) :
    (a.map f).sum = f (a.headD e) + (a.tail.map f).sum := by
  cases a with
  | nil => simp [he]
  | cons x t => simp

/-- `R` rounds play two lists of at most `R` jobs each. -/
theorem exists_roundsT (hn : 2 ≤ n) {Q QO QE Y : Finset (Fin n)} (c : PairCtx Q Y) (hO : QO ⊆ Q)
    (hE : QE ⊆ Q) (hd : Disjoint QO QE) (L : ℕ) (R : ℕ) :
    ∀ a b : List (Job n), a.length ≤ R → b.length ≤ R →
      (∀ J ∈ a, J.X ⊆ QO) → (∀ J ∈ b, J.X ⊆ QE) →
      ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
        W.length ≤ R * (2 * Y.card) + ((a.map (Job.edges L Y)).sum + (b.map (Job.edges L Y)).sum) ∧
        FixesSkel hn W ∧
        ∀ i j, IsRow i → IsCol j →
          ((∀ J ∈ b, J.act L Y i j = 1) → Rv (rep i j) W = (a.map fun J => J.act L Y i j).prod) ∧
          ((∀ J ∈ a, J.act L Y i j = 1) →
            Rv (rep i j) W = (b.map fun J => (J.act L Y i j)⁻¹).prod) := by
  induction R with
  | zero =>
    intro a b ha hb _ _
    have ha' : a = [] := List.length_eq_zero_iff.1 (by omega)
    have hb' : b = [] := List.length_eq_zero_iff.1 (by omega)
    subst ha' hb'
    exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp⟩
  | succ R ih =>
    intro a b ha hb hax hbx
    obtain ⟨W, h1, h2, h3, h4⟩ := ih a.tail b.tail (by simp; omega) (by simp; omega)
      (fun J hJ => hax J (List.mem_of_mem_tail hJ)) (fun J hJ => hbx J (List.mem_of_mem_tail hJ))
    set x := a.headD Job.emp with hx
    set y := b.headD Job.emp with hy
    have hx1 : x.X ⊆ QO := by
      rcases headD_mem_or Job.emp a with h | h
      · rw [hx, h]
        simp [Job.emp]
      · exact hax _ h
    have hy1 : y.X ⊆ QE := by
      rcases headD_mem_or Job.emp b with h | h
      · rw [hy, h]
        simp [Job.emp]
      · exact hbx _ h
    have hRv : ∀ i j, IsRow i → IsCol j →
        Rv (rep i j) (jobRoundT hn L Y x y) = x.act L Y i j * (y.act L Y i j)⁻¹ := fun i j hi hj =>
      jobRoundT_Rv hn c L (hx1.trans hO) (hy1.trans hE)
        (Finset.disjoint_of_subset_left hx1 (Finset.disjoint_of_subset_right hy1 hd)) hi hj
    have hcY := c.hY
    refine ⟨jobRoundT hn L Y x y ++ W, ?_, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact jobRoundT_isQ hn _ _ _ _ m h
      · exact h1 m h
    · have := jobRoundT_length hn L Y x y
      have ea : (a.map (Job.edges L Y)).sum = Job.edges L Y x + (a.tail.map (Job.edges L Y)).sum :=
        sum_head_tail (Job.edges L Y) Job.emp (Job.emp_edges L Y) a
      have eb : (b.map (Job.edges L Y)).sum = Job.edges L Y y + (b.tail.map (Job.edges L Y)).sum :=
        sum_head_tail (Job.edges L Y) Job.emp (Job.emp_edges L Y) b
      have hm : (R + 1) * (2 * Y.card) = R * (2 * Y.card) + 2 * Y.card := by ring
      simp only [List.length_append]
      rw [ea, eb, this, hm]
      omega
    · exact (jobRoundT_fixesSkel hn hcY _ _ _).append h3
    · intro i j hi hj
      obtain ⟨A1, A2⟩ := h4 i j hi hj
      rw [Rv_append, hRv i j hi hj]
      constructor
      · intro hb1
        have hy2 : y.act L Y i j = 1 := by
          rcases headD_mem_or Job.emp b with h | h
          · rw [hy, h, Job.emp_act]
          · exact hb1 _ h
        rw [A1 (fun J hJ => hb1 J (List.mem_of_mem_tail hJ)), hy2,
          prod_head_tail (fun J : Job n => J.act L Y i j) Job.emp (Job.emp_act L Y i j) a]
        simp [hx]
      · intro ha1
        have hx2 : x.act L Y i j = 1 := by
          rcases headD_mem_or Job.emp a with h | h
          · rw [hx, h, Job.emp_act]
          · exact ha1 _ h
        rw [A2 (fun J hJ => ha1 J (List.mem_of_mem_tail hJ)), hx2,
          prod_head_tail (fun J : Job n => (J.act L Y i j)⁻¹) Job.emp (by simp [Job.emp_act]) b]
        simp [hy]

/-! ### The jobs of a list of lists -/

/-- The key of a list: its size, and the total length of its templates. -/
def tKey (l : List Tmpl) : ℕ × ℕ := (l.length, (l.map tmplLen).sum)

/-- The bound on the edges of one job of a list. -/
def tEdges (sOf : ℕ × ℕ → ℕ) (l : List Tmpl) : ℕ :=
  2 * (tKey l).2 * geomS (tKey l).1 (sOf (tKey l))

theorem job_edges_le (X Y : Finset (Fin n)) (L : ℕ) (l : List Tmpl) (hl : l ≠ [])
    (hL : ∀ t ∈ l, tmplLen t ≤ L) (s : ℕ) (hX : X.card ≤ s) (pat : Fin n → Fin n → Tmpl)
    (hv : ∀ j ∈ Y, ∀ i ∈ X, pat j i ∈ l) :
    passEdges X Y (clampT L) pat ≤ 2 * (l.map tmplLen).sum * geomS l.length s := by
  have h1 := trieCost_le (ρ := X) (fun a => tmplLen (clampT L a)) l X.attach.toList (patsOf X Y pat).toList
    (by
      intro p hp r _
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_toList.1 hp)
      exact hv j hj r.1 r.2)
  have h2 : (l.map fun a => tmplLen (clampT L a)) = l.map tmplLen :=
    List.map_congr_left fun t ht => by rw [clampT_of_le (hL t ht)]
  have hpos : 1 ≤ l.length := List.length_pos_iff.2 hl
  have h3 : X.attach.toList.length ≤ s := by simpa using hX
  rw [h2] at h1
  refine h1.trans (Nat.mul_le_mul_left _ (geomS_mono hpos h3))

/-- All the jobs of one half of a block. -/
theorem exists_jobsT (R Y : Finset (Fin n)) (L : ℕ) (sOf : ℕ × ℕ → ℕ) :
    ∀ (ls : List (List Tmpl)) (vals : Fin n → Fin n → List Tmpl),
      (∀ l ∈ ls, l ≠ []) → (∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) →
      (∀ k ∈ ls.map tKey, 0 < sOf k) →
      (∀ i ∈ R, ∀ j ∈ Y, List.Forall₂ (· ∈ ·) (vals i j) ls) →
      ∃ js : List (Job n), js.length ≤ (ls.map fun l => R.card / sOf (tKey l) + 1).sum ∧
        (∀ J ∈ js, J.X ⊆ R) ∧
        (js.map (Job.edges L Y)).sum ≤ (ls.map fun l => (R.card / sOf (tKey l) + 1) * tEdges sOf l).sum ∧
        ∀ (F : Tmpl → Perm (Fin 24)) (i j : Fin n), i ∈ R → j ∈ Y →
          (js.map fun J => if i ∈ J.X then F (clampT L (J.pat j i)) else 1).prod =
            ((vals i j).map F).prod := by
  intro ls
  induction ls with
  | nil =>
    intro vals _ _ _ hv
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    intro F i j hi hj
    have := hv i hi j hj
    rw [List.forall₂_nil_right_iff] at this
    simp [this]
  | cons l ls ih =>
    intro vals hne hL hs hv
    have hm : tKey l ∈ (l :: ls).map tKey := by simp
    have hsp : ∀ i ∈ R, ∀ j ∈ Y, ∃ v vs, v ∈ l ∧ List.Forall₂ (· ∈ ·) vs ls ∧ vals i j = v :: vs :=
      fun i hi j hj => List.forall₂_cons_right_iff.1 (hv i hi j hj)
    obtain ⟨chunks, hch⟩ := exists_chunking (sOf (tKey l)) (hs _ hm) R
    obtain ⟨js, h1, h2, h2', h3⟩ := ih (fun i j => (vals i j).tail)
      (fun l' hl' => hne l' (List.mem_cons_of_mem _ hl'))
      (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
      (fun m hm' => hs m (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hm'))
      (fun i hi j hj => by
        obtain ⟨v, vs, _, h, he⟩ := hsp i hi j hj
        rw [he]
        exact h)
    let J₀ : Finset (Fin n) → Job n := fun X => ⟨X, fun j i => (vals i j).headD []⟩
    refine ⟨chunks.map J₀ ++ js, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.map_cons, List.sum_cons]
      have := hch.length
      omega
    · intro J hJ
      rcases List.mem_append.1 hJ with h | h
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
        exact hch.sub X hX
      · exact h2 J h
    · have hone : ∀ X ∈ chunks, (J₀ X).edges L Y ≤ tEdges sOf l := by
        intro X hX
        have hXR := hch.sub X hX
        apply job_edges_le X Y L l (hne l List.mem_cons_self)
          (hL l List.mem_cons_self) _ (hch.card X hX)
        intro j hj i hi
        obtain ⟨v, vs, hvl, _, he⟩ := hsp i (hXR hi) j hj
        simp only [J₀, he, List.headD_cons]
        exact hvl
      have hsum : ((chunks.map J₀).map (Job.edges L Y)).sum ≤ chunks.length * tEdges sOf l := by
        generalize chunks = cs at hone
        induction cs with
        | nil => simp
        | cons a t iht =>
          have h1' := hone a List.mem_cons_self
          have h2'' := iht (fun x hx => hone x (List.mem_cons_of_mem _ hx))
          simp only [List.map_cons, List.sum_cons, List.length_cons] at h2'' ⊢
          nlinarith
      have hlen := hch.length
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons]
      have := Nat.mul_le_mul_right (tEdges sOf l) hlen
      omega
    · intro F i j hi hj
      obtain ⟨v, vs, hvl, _, he⟩ := hsp i hi j hj
      have h3' := h3 F i j hi hj
      rw [he] at h3'
      simp only [List.tail_cons] at h3'
      have hhead : (chunks.map fun X => if i ∈ X then F (clampT L ((J₀ X).pat j i)) else 1).prod =
          F v := by
        have e : (J₀ · |>.pat j i) = fun _ => v := by
          funext X
          simp only [J₀, he, List.headD_cons]
        have : (fun X => if i ∈ X then F (clampT L ((J₀ X).pat j i)) else 1) =
            fun X => if i ∈ X then F v else 1 := by
          funext X
          have : (J₀ X).pat j i = v := congrFun e X
          rw [this, clampT_of_le (hL l List.mem_cons_self v hvl)]
        rw [this]
        exact chunk_prod _ chunks hch.disj (hch.cover i hi)
      rw [List.map_append, List.prod_append, h3', he, List.map_cons, List.prod_cons, List.map_map]
      congr 1

theorem jobsT_length_le (A S : ℕ) (hA : A ≤ S / 2) (sOf : ℕ × ℕ → ℕ) (ls : List (List Tmpl)) :
    (ls.map fun l => A / sOf (tKey l) + 1).sum ≤ trieRounds S sOf (ls.map tKey) := by
  induction ls with
  | nil => simp [trieRounds]
  | cons l t ih =>
    simp only [trieRounds, List.map_cons, List.sum_cons] at ih ⊢
    have := Nat.div_le_div_right (c := sOf (tKey l)) hA
    omega

theorem jobsT_edges_le (A S : ℕ) (hA : A ≤ S / 2) (sOf : ℕ × ℕ → ℕ) (ls : List (List Tmpl)) :
    (ls.map fun l => (A / sOf (tKey l) + 1) * tEdges sOf l).sum ≤ trieSlots S sOf (ls.map tKey) := by
  induction ls with
  | nil => simp [trieSlots]
  | cons l t ih =>
    simp only [trieSlots, List.map_cons, List.sum_cons, tEdges] at ih ⊢
    have h1 := Nat.div_le_div_right (c := sOf (tKey l)) hA
    have h2 := Nat.mul_le_mul_right (2 * (tKey l).2 * geomS (tKey l).1 (sOf (tKey l)))
      (Nat.add_le_add_right h1 1)
    omega

/-! ### A program -/

/-- **The action of a program, with tries.** -/
theorem programT_main (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ × ℕ → ℕ)
    (hs : ∀ k ∈ ls.map tKey, 0 < sOf k) (S : ℕ)
    {QO QE Y : Finset (Fin n)} (c : PairCtx (QO ∪ QE) Y) (hd : Disjoint QO QE)
    (hcO : QO.card ≤ S / 2) (hcE : QE.card ≤ S / 2) (vals : Fin n → Fin n → List Tmpl)
    (hv : ∀ i ∈ QO ∪ QE, ∀ j ∈ Y, List.Forall₂ (· ∈ ·) (vals i j) ls) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
      W.length ≤ trieRounds S sOf (ls.map tKey) * (2 * Y.card) + 2 * trieSlots S sOf (ls.map tKey) ∧
      FixesSkel hn W ∧ ∀ i j, IsRow i → IsCol j →
        Rv (rep i j) W =
          if i ∈ QO ∧ j ∈ Y then ((vals i j).map eT).prod
          else if i ∈ QE ∧ j ∈ Y then (((vals i j).map eT).prod)⁻¹
          else if Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y then
            ((vals (Fin.rev j) (Fin.rev i)).map eM).prod
          else if Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y then
            (((vals (Fin.rev j) (Fin.rev i)).map eM).prod)⁻¹
          else 1 := by
  have hO : QO ⊆ QO ∪ QE := Finset.subset_union_left
  have hE : QE ⊆ QO ∪ QE := Finset.subset_union_right
  obtain ⟨jsO, o1, o2, o2', o3⟩ := exists_jobsT QO Y L sOf ls vals hne hL hs
    (fun i hi j hj => hv i (hO hi) j hj)
  obtain ⟨jsE, e1, e2, e2', e3⟩ := exists_jobsT QE Y L sOf ls vals hne hL hs
    (fun i hi j hj => hv i (hE hi) j hj)
  set R := trieRounds S sOf (ls.map tKey) with hR
  obtain ⟨W, w1, w2, w3, w4⟩ := exists_roundsT hn c hO hE hd L R jsO jsE.reverse
    (o1.trans (jobsT_length_le _ S hcO sOf ls))
    (by rw [List.length_reverse]; exact e1.trans (jobsT_length_le _ S hcE sOf ls))
    o2 (fun J hJ => e2 J (List.mem_reverse.1 hJ))
  refine ⟨W, w1, ?_, w3, ?_⟩
  · have h1 := o2'.trans (jobsT_edges_le _ S hcO sOf ls)
    have h2 := e2'.trans (jobsT_edges_le _ S hcE sOf ls)
    have h3 : ((jsE.reverse).map (Job.edges L Y)).sum = (jsE.map (Job.edges L Y)).sum :=
      ((List.reverse_perm jsE).map _).sum_eq
    rw [h3] at w2
    omega
  intro i j hi hj
  obtain ⟨A1, A2⟩ := w4 i j hi hj
  have offO : ∀ J ∈ jsO, ¬ (i ∈ QO ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(o2 J hJ) h.1, h.2⟩) (fun h => h₂ ⟨(o2 J hJ) h.1, h.2⟩)
  have offE : ∀ J ∈ jsE, ¬ (i ∈ QE ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(e2 J hJ) h.1, h.2⟩) (fun h => h₂ ⟨(e2 J hJ) h.1, h.2⟩)
  by_cases c1 : i ∈ QO ∧ j ∈ Y
  · have hnE : ¬ (i ∈ QE ∧ j ∈ Y) := fun h => Finset.disjoint_left.1 hd c1.1 h.1
    have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c1.2 (hE h.1)
    rw [if_pos c1, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) hnE hnE'), ← o3 eT i j c1.1 c1.2]
    congr 1
    exact List.map_congr_left fun J hJ =>
      Job.act_target c L ((o2 J hJ).trans hO) c1.2
  · rw [if_neg c1]
    by_cases c2 : i ∈ QE ∧ j ∈ Y
    · have hnO' : ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c2.2 (hO h.1)
      rw [if_pos c2, A2 (fun J hJ => offO J hJ c1 hnO'), prod_reverse_inv, ← e3 eT i j c2.1 c2.2]
      congr 2
      exact List.map_congr_left fun J hJ =>
        Job.act_target c L ((e2 J hJ).trans hE) c2.2
    · rw [if_neg c2]
      by_cases c3 : Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y
      · have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) :=
          fun h => Finset.disjoint_left.1 hd c3.1 h.1
        rw [if_pos c3, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) c2 hnE'),
          ← o3 eM _ _ c3.1 c3.2]
        congr 1
        exact List.map_congr_left fun J hJ =>
          Job.act_mirror c L ((o2 J hJ).trans hO) c3.2
      · rw [if_neg c3]
        by_cases c4 : Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y
        · rw [if_pos c4, A2 (fun J hJ => offO J hJ c1 c3), prod_reverse_inv,
            ← e3 eM _ _ c4.1 c4.2]
          congr 2
          exact List.map_congr_left fun J hJ =>
            Job.act_mirror c L ((e2 J hJ).trans hE) c4.2
        · rw [if_neg c4, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) c2 c4)]
          apply List.prod_eq_one
          intro x hx
          obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
          exact offO J hJ c1 c3

/-- **A program solves any even targets on the orbits of a block.** -/
theorem programT_solve (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ × ℕ → ℕ)
    (hs : ∀ k ∈ ls.map tKey, 0 < sOf k) (S : ℕ) (hS : Even S)
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (hQ : Q.card ≤ S) (π : Fin n → Fin n → Perm (Fin 24))
    (hπ : ∀ i j, Perm.sign (π i j) = 1) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
      W.length ≤ trieRounds S sOf (ls.map tKey) * (2 * Y.card) + 2 * trieSlots S sOf (ls.map tKey) ∧
      FixesSkel hn W ∧ ∀ i j, IsRow i → IsCol j →
        Rv (rep i j) W =
          if (i ∈ Q ∧ j ∈ Y) ∨ (Fin.rev j ∈ Q ∧ Fin.rev i ∈ Y) then π i j else 1 := by
  obtain ⟨QO, QE, hU, hd, hcO, hcE⟩ := exists_split Q S hS hQ
  subst hU
  choose ch h1 h2 h3 using huniv
  let vals : Fin n → Fin n → List Tmpl := fun i j =>
    if i ∈ QO then ch (π i j) (π (Fin.rev j) (Fin.rev i)) (hπ _ _) (hπ _ _)
    else ch (π i j)⁻¹ (π (Fin.rev j) (Fin.rev i))⁻¹ (by simp [hπ]) (by simp [hπ])
  have hvO : ∀ i j, i ∈ QO → vals i j = ch (π i j) (π (Fin.rev j) (Fin.rev i)) (hπ _ _) (hπ _ _) :=
    fun i j hi => if_pos hi
  have hvE : ∀ i j, i ∈ QE → vals i j =
      ch (π i j)⁻¹ (π (Fin.rev j) (Fin.rev i))⁻¹ (by simp [hπ]) (by simp [hπ]) :=
    fun i j hi => if_neg (Finset.disjoint_right.1 hd hi)
  obtain ⟨W, w1, w2, w3, w4⟩ := programT_main hn ls hne L hL sOf hs S c hd hcO hcE vals
    (fun i _ j _ => by
      by_cases hi : i ∈ QO
      · rw [hvO i j hi]; exact h1 _ _ _ _
      · simp only [vals, if_neg hi]; exact h1 _ _ _ _)
  refine ⟨W, w1, w2, w3, ?_⟩
  intro i j hi hj
  rw [w4 i j hi hj]
  have hrr : ∀ x : Fin n, Fin.rev (Fin.rev x) = x := Fin.rev_rev
  by_cases c1 : i ∈ QO ∧ j ∈ Y
  · rw [if_pos c1, if_pos (Or.inl ⟨Finset.mem_union_left _ c1.1, c1.2⟩), hvO i j c1.1, h2]
  · rw [if_neg c1]
    by_cases c2 : i ∈ QE ∧ j ∈ Y
    · rw [if_pos c2, if_pos (Or.inl ⟨Finset.mem_union_right _ c2.1, c2.2⟩), hvE i j c2.1, h2,
        inv_inv]
    · rw [if_neg c2]
      by_cases c3 : Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y
      · rw [if_pos c3, if_pos (Or.inr ⟨Finset.mem_union_left _ c3.1, c3.2⟩), hvO _ _ c3.1, h3,
          hrr, hrr]
      · rw [if_neg c3]
        by_cases c4 : Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y
        · rw [if_pos c4, if_pos (Or.inr ⟨Finset.mem_union_right _ c4.1, c4.2⟩), hvE _ _ c4.1, h3,
            hrr, hrr, inv_inv]
        · rw [if_neg c4, if_neg]
          rintro (⟨h, hy⟩ | ⟨h, hy⟩)
          · rcases Finset.mem_union.1 h with h | h
            · exact c1 ⟨h, hy⟩
            · exact c2 ⟨h, hy⟩
          · rcases Finset.mem_union.1 h with h | h
            · exact c3 ⟨h, hy⟩
            · exact c4 ⟨h, hy⟩

/-! ### All programs -/

/-- The programs of the first `m` blocks. -/
theorem exists_programsT (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ × ℕ → ℕ)
    (hs : ∀ k ∈ ls.map tKey, 0 < sOf k) (S : ℕ) (hS0 : 0 < S) (hS : Even S)
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (π : Fin n → Fin n → Perm (Fin 24)) (hπ : ∀ i j, Perm.sign (π i j) = 1) (m : ℕ) :
    ∃ P : Word n, (∀ m ∈ P, IsQ m) ∧
      P.length ≤ ∑ t ∈ Finset.range m, (trieRounds S sOf (ls.map tKey) * (2 * (blockY n S t).card) +
        2 * trieSlots S sOf (ls.map tKey)) ∧
      FixesSkel hn P ∧ ∀ i j, IsRow i → IsCol j →
        ((∃ t, t < m ∧ Handled n S t i j) → Rv (rep i j) P = π i j) ∧
        ((¬ ∃ t, t < m ∧ Handled n S t i j) → Rv (rep i j) P = 1) := by
  classical
  induction m with
  | zero => exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp⟩
  | succ m ih =>
    obtain ⟨P, p1, p2, p3, p4⟩ := ih
    obtain ⟨W, w1, w2, w3, w4⟩ := programT_solve hn ls hne L hL sOf hs S hS huniv
      (block_ctx (n := n) S m) (card_blockQ_le S m hS0) π hπ
    refine ⟨P ++ W, ?_, ?_, p3.append w3, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact p1 x h
      · exact w1 x h
    · rw [Finset.sum_range_succ, List.length_append]
      omega
    · intro i j hi hj
      obtain ⟨A1, A2⟩ := p4 i j hi hj
      have hW := w4 i j hi hj
      rw [Rv_append, hW]
      by_cases hH : Handled n S m i j
      · have hno : ¬ ∃ t, t < m ∧ Handled n S t i j := by
          rintro ⟨t, ht, h⟩
          have := handled_unique hi h hH
          omega
        have hH' : (i ∈ blockQ n S m ∧ j ∈ blockY n S m) ∨
            (Fin.rev j ∈ blockQ n S m ∧ Fin.rev i ∈ blockY n S m) := hH
        rw [if_pos hH', A2 hno, one_mul]
        exact ⟨fun _ => rfl, fun h => absurd ⟨m, by omega, hH⟩ h⟩
      · have hH' : ¬ ((i ∈ blockQ n S m ∧ j ∈ blockY n S m) ∨
            (Fin.rev j ∈ blockQ n S m ∧ Fin.rev i ∈ blockY n S m)) := hH
        rw [if_neg hH', mul_one]
        constructor
        · rintro ⟨t, ht, h⟩
          apply A1
          refine ⟨t, ?_, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | rfl
          · exact h'
          · exact absurd h hH
        · intro h
          exact A2 fun ⟨t, ht, h'⟩ => h ⟨t, by omega, h'⟩

/-! ### The theorem -/

/-- **Every position is solved in `trieExactW` quarter turns**, given universal lists. -/
theorem solve_trie (hn : 3 ≤ n) (ls : List (List Tmpl))
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (S : ℕ) (hS0 : 0 < S) (hS : Even S) (sOf : ℕ × ℕ → ℕ) (hs : ∀ k ∈ ls.map tKey, 0 < sOf k)
    (L : ℕ) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L)
    (g : Perm (Sticker n)) (hg : g ∈ cubeGroup n) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ trieExactW n S sOf (ls.map tKey) ∧
      Word.eval w * g = 1 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hne : ∀ l ∈ ls, l ≠ [] := by
    intro l hl he
    obtain ⟨ch, h1, _⟩ := huniv 1 1 (by simp) (by simp)
    obtain ⟨a, ha⟩ := forall₂_right_nonempty h1 l hl
    simp [he] at ha
  obtain ⟨w₀, hw₀, rfl⟩ := word_of_mem g hg
  obtain ⟨Wp, a₁, ha₁, hpQ, ha₁Q, hplen, ha₁E, hskC, hskE, hskZ⟩ := exists_prep hn w₀ hw₀
  let π : Fin n → Fin n → Perm (Fin 24) := fun i j => (Rv (rep i j) a₁)⁻¹
  have hπ : ∀ i j, Perm.sign (π i j) = 1 := fun i j => by
    simp only [π]
    rw [Perm.sign_inv]
    exact sign_Rv _ _ ha₁E
  obtain ⟨P, p1, p2, p3, p4⟩ := exists_programsT hn2 ls hne L hL sOf hs S hS0 hS huniv π hπ
    ((n / 2 - 1) / S + 1)
  have hun := fun i j => universal (π i j) (hπ i j)
  choose T hT1 hT2 using hun
  obtain ⟨Wb, b1, b2, b3, b4⟩ := exists_cleanup hn2 T hT1 (badOrbits n S).toList
    (Finset.nodup_toList _) (fun p hp => by
      obtain ⟨x, y⟩ := p
      have := mem_badOrbits.1 (Finset.mem_toList.1 hp)
      exact ⟨this.1, this.2.1⟩)
  rw [Finset.length_toList] at b2
  have hcard := card_badOrbits_le hn2 S hS0
  -- the length of the programs
  set R := trieRounds S sOf (ls.map tKey) with hR
  set C := trieSlots S sOf (ls.map tKey) with hC
  have hsum : (∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), (R * (2 * (blockY n S t).card) + 2 * C)) ≤
      R * ((n / 2 - 1) ^ 2 / S) + 2 * ((n / 2 - 1) / S + 1) * C := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
    have h1 : ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * (blockY n S t).card ≤
        ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * ((n / 2 - 1) - (t + 1) * S) :=
      Finset.sum_le_sum fun t _ => Nat.mul_le_mul_left _ (card_blockY_le S t hS0)
    have h2 := sum_blocks_le S hS0 (n / 2 - 1)
    have h3 : ((n / 2 - 1) / S + 1) * (2 * C) = 2 * ((n / 2 - 1) / S + 1) * C := by ring
    have h4 := Nat.mul_le_mul_left R (h1.trans h2)
    omega
  have hPlen : P.length ≤ R * ((n / 2 - 1) ^ 2 / S) + 2 * ((n / 2 - 1) / S + 1) * C := p2.trans hsum
  have hfQ : ∀ m ∈ Wb ++ P, IsQ m := by
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact b1 m h
    · exact p1 m h
  have hfS : FixesSkel hn2 (Wb ++ P) := b3.append p3
  refine ⟨(Wb ++ P) ++ Wp, ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hfQ m h
    · exact hpQ m h
  · simp only [trieExactW, List.length_append, ← hR, ← hC]
    have : 2200 * (badOrbits n S).card ≤ 2200 * ((n / 2 - 1) * (S + 2)) :=
      Nat.mul_le_mul_left _ hcard
    omega
  · have hval : Word.eval ((Wb ++ P) ++ Wp) * Word.eval w₀ = Word.eval ((Wb ++ P) ++ a₁) := by
      rw [ha₁]
      simp only [Word.eval_append, _root_.mul_assoc]
    rw [hval]
    have hWQ : ∀ m ∈ (Wb ++ P) ++ a₁, IsQ m := by
      intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact hfQ m h
      · exact ha₁Q m h
    apply eval_eq_one_of_orbits hn _ hWQ
    · intro i j hi hj k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [word_Rv _ a₁ ha₁Q, word_Rv _ P p1]
      obtain ⟨A1, A2⟩ := p4 i j hi hj
      by_cases hH : ∃ t, t < (n / 2 - 1) / S + 1 ∧ Handled n S t i j
      · have hgood := (exists_handled_iff hi).1 hH
        have hnb : (i, j) ∉ (badOrbits n S).toList := fun h =>
          (mem_badOrbits.1 (Finset.mem_toList.1 h)).2.2 hgood
        rw [A1 hH, (b4 i j hi hj _).2 hnb]
        simp [π]
      · have hbad : (i, j) ∈ (badOrbits n S).toList := Finset.mem_toList.2
          (mem_badOrbits.2 ⟨hi, hj, fun h => hH ((exists_handled_iff hi).2 h)⟩)
        rw [A2 hH, Perm.one_apply, (b4 i j hi hj _).1 hbad, hT2]
        simp [π]
    · intro k
      rw [Word.eval_append, Perm.mul_apply, hskC k]
      exact hfS.1 (layerOf hn 2) (Or.inl rfl) k
    · intro j hj k
      rw [Word.eval_append, Perm.mul_apply, hskE j hj k]
      exact hfS.1 j (Or.inr hj) k
    · intro m hm k
      rw [Word.eval_append, Perm.mul_apply, hskZ m hm k]
      exact hfS.2 m hm k

/-- **Upper bound of the round scheme with trie slots**, for abstract universal lists. -/
theorem godLabelled_le_trieExactW (μ : Metric) (hn : 3 ≤ n) (ls : List (List Tmpl))
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (S : ℕ) (hS0 : 0 < S) (hS : Even S) (sOf : ℕ × ℕ → ℕ) (hs : ∀ k ∈ ls.map tKey, 0 < sOf k)
    (L : ℕ) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) :
    godLabelled μ n ≤ trieExactW n S sOf (ls.map tKey) := by
  apply Nat.sInf_le
  intro g hg
  obtain ⟨w, h1, h2, h3⟩ := solve_trie hn ls huniv S hS0 hS sOf hs L hL g hg
  exact ⟨w, fun m hm => allows_of_isQ μ m (h1 m hm), h2, h3⟩

/-! ### The form with a uniform slot bound

The same formula as `exactW`, with `m ^ s * (4 * L) ≤ Cslot` in place of `m ^ s * (2 * s * L) ≤ Cslot`. -/

theorem tmplSum_le (l : List Tmpl) (L : ℕ) (hL : ∀ t ∈ l, tmplLen t ≤ L) :
    (l.map tmplLen).sum ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h1 := hL a List.mem_cons_self
    have h2 := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- The edges of a job of a list, for `m ≥ 2`. -/
theorem tEdges_le_uniform (l : List Tmpl) (L s : ℕ) (hm : 2 ≤ l.length)
    (hL : ∀ t ∈ l, tmplLen t ≤ L) :
    2 * (l.map tmplLen).sum * geomS l.length s ≤ l.length ^ s * (4 * L) := by
  have h1 := tmplSum_le l L hL
  have h2 := geomS_mul l.length s (by omega)
  have h3 : l.length * geomS l.length s ≤ 2 * l.length ^ s := by
    obtain ⟨k, hk⟩ : ∃ k, l.length = k + 2 := ⟨l.length - 2, by omega⟩
    rw [← h2, hk]
    simp only [show k + 2 - 1 = k + 1 by omega]
    nlinarith [Nat.zero_le (geomS (k + 2) s), Nat.zero_le k, Nat.zero_le (k * geomS (k + 2) s)]
  calc 2 * (l.map tmplLen).sum * geomS l.length s
      ≤ 2 * (l.length * L) * geomS l.length s := by gcongr
    _ = (l.length * geomS l.length s) * (2 * L) := by ring
    _ ≤ (2 * l.length ^ s) * (2 * L) := Nat.mul_le_mul_right _ h3
    _ = _ := by ring

theorem trieRounds_map (S : ℕ) (sOf : ℕ → ℕ) (ls : List (List Tmpl)) :
    trieRounds S (fun k => sOf k.1) (ls.map tKey) = exactRounds S sOf (ls.map List.length) := by
  simp [trieRounds, exactRounds, tKey, Function.comp_def]

theorem trieSlots_le_uniform (S : ℕ) (sOf : ℕ → ℕ) (L Cslot : ℕ) (ls : List (List Tmpl))
    (hm : ∀ l ∈ ls, 2 ≤ l.length) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (4 * L) ≤ Cslot) :
    trieSlots S (fun k => sOf k.1) (ls.map tKey) ≤ exactRounds S sOf (ls.map List.length) * Cslot := by
  induction ls with
  | nil => simp [trieSlots, exactRounds]
  | cons l t ih =>
    have h := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (fun x hx => hC x (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hx))
    simp only [trieSlots, exactRounds, List.map_cons, List.sum_cons, tKey] at h ⊢
    have h1 := tEdges_le_uniform l L (sOf l.length) (hm l List.mem_cons_self) (hL l List.mem_cons_self)
    have h2 := hC l.length (by simp)
    have h3 := Nat.mul_le_mul_left (S / 2 / sOf l.length + 1) (h1.trans h2)
    refine (Nat.add_le_add h3 h).trans (le_of_eq ?_)
    ring

/-- **`exactW` with trie slots**: the slot hypothesis of `godLabelled_le_exactW` without the factor `s`. -/
theorem godLabelled_le_exactW_trie (μ : Metric) (hn : 3 ≤ n) (ls : List (List Tmpl))
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (hm : ∀ l ∈ ls, 2 ≤ l.length)
    (S : ℕ) (hS0 : 0 < S) (hS : Even S) (sOf : ℕ → ℕ) (hs : ∀ m ∈ ls.map List.length, 0 < sOf m)
    (L Cslot : ℕ) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (4 * L) ≤ Cslot) :
    godLabelled μ n ≤ exactW n S Cslot sOf (ls.map List.length) := by
  have h := godLabelled_le_trieExactW μ hn ls huniv S hS0 hS (fun k => sOf k.1) (by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hk
    exact hs _ (List.mem_map_of_mem hl)) L hL
  refine h.trans ?_
  have h1 := trieSlots_le_uniform S sOf L Cslot ls hm hL hC
  rw [trieExactW, trieRounds_map, exactW]
  set R := exactRounds S sOf (ls.map List.length)
  set q := (n / 2 - 1) / S + 1
  have h2 : 2 * q * trieSlots S (fun k => sOf k.1) (ls.map tKey) ≤ 2 * q * (R * Cslot) :=
    Nat.mul_le_mul_left _ h1
  have e : R * ((n / 2 - 1) ^ 2 / S + 2 * q * Cslot) = R * ((n / 2 - 1) ^ 2 / S) + 2 * q * (R * Cslot) := by
    ring
  rw [e]
  omega

end RubiksGN
