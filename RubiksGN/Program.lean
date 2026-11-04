import RubiksGN.Rounds
import RubiksGN.ExactCost

/-!
# A program: the rounds of one coarse block

The rows of a block are split in two halves. Each half runs a list of *jobs*, one job for each chunk
of the rows and each list of templates: `QO` runs the lists in order, `QE` in reverse order. A round
plays one job of each half, so `QO` sees the product of the `eT`, and `QE` sees its inverse.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### Values are templates -/

/-- Cut a template off when it is too long; only a device to get the uniform bound of `passW_length_le`
when the values are all templates. It does nothing on the templates in use. -/
def clampT (L : ℕ) (t : Tmpl) : Tmpl := if tmplLen t ≤ L then t else []

theorem clampT_len (L : ℕ) (t : Tmpl) : tmplLen (clampT L t) ≤ L := by
  unfold clampT
  split_ifs with h
  · exact h
  · simp [tmplLen]

theorem clampT_of_le {L : ℕ} {t : Tmpl} (h : tmplLen t ≤ L) : clampT L t = t := if_pos h

/-- The number of patterns, when all values come from a list. -/
theorem patsOf_card_le_list (X Y : Finset (Fin n)) (pat : Fin n → Fin n → Tmpl) (l : List Tmpl)
    (h : ∀ j ∈ Y, ∀ i ∈ X, pat j i ∈ l) : (patsOf X Y pat).card ≤ l.length ^ X.card := by
  have hsub : patsOf X Y pat ⊆ Fintype.piFinset (fun _ : X => l.toFinset) := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    rw [Fintype.mem_piFinset]
    intro i
    exact List.mem_toFinset.2 (h j hj i.1 i.2)
  calc (patsOf X Y pat).card ≤ _ := Finset.card_le_card hsub
    _ = l.toFinset.card ^ X.card := by simp [Fintype.card_piFinset]
    _ ≤ _ := Nat.pow_le_pow_left (List.toFinset_card_le l) _

/-! ### Jobs -/

/-- A job: a chunk of rows, and the value of each entry. `pat j i` is the value of the entry `(i, j)`. -/
structure Job (n : ℕ) where
  X : Finset (Fin n)
  pat : Fin n → Fin n → Tmpl

/-- The empty job, used as padding. -/
def Job.emp : Job n := ⟨∅, fun _ _ => []⟩

/-- The cost of the slots of a job. -/
noncomputable def Job.cost (L : ℕ) (Y : Finset (Fin n)) (J : Job n) : ℕ :=
  (patsOf J.X Y J.pat).card * (2 * J.X.card * L)

/-- The action of a job on an orbit, in a pass of direction `true`. -/
def Job.act (L : ℕ) (Y : Finset (Fin n)) (J : Job n) (i j : Fin n) : Perm (Fin 24) :=
  if i ∈ J.X ∧ j ∈ Y then eT (clampT L (J.pat j i))
  else if Fin.rev j ∈ J.X ∧ Fin.rev i ∈ Y then eM (clampT L (J.pat (Fin.rev i) (Fin.rev j)))
  else 1

theorem Job.emp_act (L : ℕ) (Y : Finset (Fin n)) (i j : Fin n) : (Job.emp : Job n).act L Y i j = 1 := by
  simp [Job.act, Job.emp]

theorem Job.emp_cost (L : ℕ) (Y : Finset (Fin n)) : (Job.emp : Job n).cost L Y = 0 := by
  simp [Job.cost, Job.emp]

theorem Job.act_target {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (L : ℕ) {J : Job n} (hX : J.X ⊆ Q)
    {i j : Fin n} (hj : j ∈ Y) :
    J.act L Y i j = if i ∈ J.X then eT (clampT L (J.pat j i)) else 1 := by
  have h : ¬ (Fin.rev j ∈ J.X ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem hj (hX h.1)
  simp only [Job.act, hj, and_true, if_neg h]

theorem Job.act_mirror {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (L : ℕ) {J : Job n} (hX : J.X ⊆ Q)
    {i j : Fin n} (hi : Fin.rev i ∈ Y) :
    J.act L Y i j = if Fin.rev j ∈ J.X then eM (clampT L (J.pat (Fin.rev i) (Fin.rev j))) else 1 := by
  have h : ¬ (i ∈ J.X ∧ j ∈ Y) := fun h => c.not_rev_mem' (hX h.1) hi
  simp only [Job.act, hi, and_true, if_neg h]

theorem Job.act_off (L : ℕ) (Y : Finset (Fin n)) {J : Job n} {i j : Fin n}
    (h₁ : ¬ (i ∈ J.X ∧ j ∈ Y)) (h₂ : ¬ (Fin.rev j ∈ J.X ∧ Fin.rev i ∈ Y)) : J.act L Y i j = 1 := by
  simp only [Job.act, if_neg h₁, if_neg h₂]

/-- The round of two jobs. -/
noncomputable def jobRound (hn : 2 ≤ n) (L : ℕ) (Y : Finset (Fin n)) (J₁ J₂ : Job n) : Word n :=
  roundW hn J₁.X J₂.X Y (clampT L) (clampT L) J₁.pat J₂.pat

/-- A round acts by the first job, and by the inverse of the second. -/
theorem jobRound_Rv (hn : 2 ≤ n) {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (L : ℕ) {J₁ J₂ : Job n}
    (h₁ : J₁.X ⊆ Q) (h₂ : J₂.X ⊆ Q) (hd : Disjoint J₁.X J₂.X) {i j : Fin n} (hi : IsRow i)
    (hj : IsCol j) :
    Rv (rep i j) (jobRound hn L Y J₁ J₂) = J₁.act L Y i j * (J₂.act L Y i j)⁻¹ := by
  rw [jobRound, round_Rv hn c h₁ h₂ hd _ _ _ _ hi hj]
  by_cases ha : i ∈ J₁.X ∧ j ∈ Y
  · have hb : J₂.act L Y i j = 1 := Job.act_off L Y
      (fun h => Finset.disjoint_left.1 hd ha.1 h.1) (fun h => c.not_rev_mem ha.2 (h₂ h.1))
    rw [if_pos ha, hb, Job.act, if_pos ha]
    simp
  · rw [if_neg ha]
    by_cases hb : i ∈ J₂.X ∧ j ∈ Y
    · have ha' : J₁.act L Y i j = 1 := Job.act_off L Y ha (fun h => c.not_rev_mem hb.2 (h₁ h.1))
      rw [if_pos hb, ha', Job.act, if_pos hb]
      simp
    · rw [if_neg hb]
      by_cases hc : Fin.rev j ∈ J₁.X ∧ Fin.rev i ∈ Y
      · have hb' : J₂.act L Y i j = 1 := Job.act_off L Y hb
          (fun h => Finset.disjoint_left.1 hd hc.1 h.1)
        rw [if_pos hc, hb', Job.act, if_neg ha, if_pos hc]
        simp
      · rw [if_neg hc]
        have ha' : J₁.act L Y i j = 1 := Job.act_off L Y ha hc
        by_cases hd' : Fin.rev j ∈ J₂.X ∧ Fin.rev i ∈ Y
        · rw [if_pos hd', ha', Job.act, if_neg hb, if_pos hd']
          simp
        · rw [if_neg hd', ha', Job.act_off L Y hb hd']
          simp

theorem jobRound_length_le (hn : 2 ≤ n) (L : ℕ) (Y : Finset (Fin n)) (J₁ J₂ : Job n) :
    (jobRound hn L Y J₁ J₂).length ≤ 2 * Y.card + (J₁.cost L Y + J₂.cost L Y) :=
  roundW_length_le hn J₁.X J₂.X Y _ _ J₁.pat J₂.pat L (clampT_len L) (clampT_len L)

/-! ### Zipping two job lists into rounds -/

theorem prod_head_tail {β G : Type*} [Monoid G] (f : β → G) (e : β) (he : f e = 1) (a : List β) :
    (a.map f).prod = f (a.headD e) * (a.tail.map f).prod := by
  cases a with
  | nil => simp [he]
  | cons x t => simp

theorem headD_mem_or {β : Type*} (e : β) (a : List β) : a.headD e = e ∨ a.headD e ∈ a := by
  cases a with
  | nil => exact Or.inl rfl
  | cons x t => exact Or.inr List.mem_cons_self

/-- `R` rounds play two lists of at most `R` jobs each. An orbit that only one list touches sees that
list's product. -/
theorem exists_rounds (hn : 2 ≤ n) {Q QO QE Y : Finset (Fin n)} (c : PairCtx Q Y) (hO : QO ⊆ Q)
    (hE : QE ⊆ Q) (hd : Disjoint QO QE) (L Cslot : ℕ) (R : ℕ) :
    ∀ a b : List (Job n), a.length ≤ R → b.length ≤ R →
      (∀ J ∈ a, J.X ⊆ QO ∧ J.cost L Y ≤ Cslot) → (∀ J ∈ b, J.X ⊆ QE ∧ J.cost L Y ≤ Cslot) →
      ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧ W.length ≤ R * (2 * Y.card + 2 * Cslot) ∧ FixesSkel hn W ∧
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
    have hx1 : x.X ⊆ QO ∧ x.cost L Y ≤ Cslot := by
      rcases headD_mem_or Job.emp a with h | h
      · rw [hx, h]
        exact ⟨by simp [Job.emp], by rw [Job.emp_cost]; omega⟩
      · exact hax _ h
    have hy1 : y.X ⊆ QE ∧ y.cost L Y ≤ Cslot := by
      rcases headD_mem_or Job.emp b with h | h
      · rw [hy, h]
        exact ⟨by simp [Job.emp], by rw [Job.emp_cost]; omega⟩
      · exact hbx _ h
    have hRv : ∀ i j, IsRow i → IsCol j →
        Rv (rep i j) (jobRound hn L Y x y) = x.act L Y i j * (y.act L Y i j)⁻¹ := fun i j hi hj =>
      jobRound_Rv hn c L (hx1.1.trans hO) (hy1.1.trans hE)
        (Finset.disjoint_of_subset_left hx1.1 (Finset.disjoint_of_subset_right hy1.1 hd)) hi hj
    have hcY := c.hY
    refine ⟨jobRound hn L Y x y ++ W, ?_, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact roundW_isQ hn _ _ _ _ _ _ _ m h
      · exact h1 m h
    · have := jobRound_length_le hn L Y x y
      simp only [List.length_append]
      nlinarith [hx1.2, hy1.2]
    · exact (roundW_fixesSkel hn hcY _ _ _ _).append h3
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

/-- Exactly the chunk of the row acts. -/
theorem chunk_prod {G : Type*} [Monoid G] (g : G) (chunks : List (Finset (Fin n)))
    (hd : chunks.Pairwise Disjoint) {i : Fin n} (hi : ∃ X ∈ chunks, i ∈ X) :
    (chunks.map fun X => if i ∈ X then g else 1).prod = g := by
  induction chunks with
  | nil => obtain ⟨X, hX, _⟩ := hi; simp at hX
  | cons X t ih =>
    obtain ⟨hX, ht⟩ := List.pairwise_cons.1 hd
    simp only [List.map_cons, List.prod_cons]
    by_cases hiX : i ∈ X
    · have : (t.map fun X => if i ∈ X then g else 1).prod = 1 := by
        apply List.prod_eq_one
        intro y hy
        obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hy
        rw [if_neg (fun h => Finset.disjoint_left.1 (hX Z hZ) hiX h)]
      rw [if_pos hiX, this, mul_one]
    · rw [if_neg hiX, one_mul]
      apply ih ht
      obtain ⟨Z, hZ, hiZ⟩ := hi
      rcases List.mem_cons.1 hZ with rfl | hZ'
      · exact absurd hiZ hiX
      · exact ⟨Z, hZ', hiZ⟩

/-- All the jobs of one half of a block. -/
theorem exists_jobs (R Y : Finset (Fin n)) (L Cslot : ℕ) (sOf : ℕ → ℕ) :
    ∀ (ls : List (List Tmpl)) (vals : Fin n → Fin n → List Tmpl),
      (∀ l ∈ ls, l ≠ []) → (∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) →
      (∀ m ∈ ls.map List.length, 0 < sOf m) →
      (∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) →
      (∀ i ∈ R, ∀ j ∈ Y, List.Forall₂ (· ∈ ·) (vals i j) ls) →
      ∃ js : List (Job n), js.length ≤ (ls.map fun l => R.card / sOf l.length + 1).sum ∧
        (∀ J ∈ js, J.X ⊆ R ∧ J.cost L Y ≤ Cslot) ∧
        ∀ (F : Tmpl → Perm (Fin 24)) (i j : Fin n), i ∈ R → j ∈ Y →
          (js.map fun J => if i ∈ J.X then F (clampT L (J.pat j i)) else 1).prod =
            ((vals i j).map F).prod := by
  intro ls
  induction ls with
  | nil =>
    intro vals _ _ _ _ hv
    refine ⟨[], by simp, by simp, ?_⟩
    intro F i j hi hj
    have := hv i hi j hj
    rw [List.forall₂_nil_right_iff] at this
    simp [this]
  | cons l ls ih =>
    intro vals hne hL hs hC hv
    have hm : l.length ∈ (l :: ls).map List.length := by simp
    have hsp : ∀ i ∈ R, ∀ j ∈ Y, ∃ v vs, v ∈ l ∧ List.Forall₂ (· ∈ ·) vs ls ∧ vals i j = v :: vs :=
      fun i hi j hj => List.forall₂_cons_right_iff.1 (hv i hi j hj)
    obtain ⟨chunks, hch⟩ := exists_chunking (sOf l.length) (hs _ hm) R
    obtain ⟨js, h1, h2, h3⟩ := ih (fun i j => (vals i j).tail)
      (fun l' hl' => hne l' (List.mem_cons_of_mem _ hl'))
      (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
      (fun m hm' => hs m (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hm'))
      (fun m hm' => hC m (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hm'))
      (fun i hi j hj => by
        obtain ⟨v, vs, _, h, he⟩ := hsp i hi j hj
        rw [he]
        exact h)
    let J₀ : Finset (Fin n) → Job n := fun X => ⟨X, fun j i => (vals i j).headD []⟩
    refine ⟨chunks.map J₀ ++ js, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.map_cons, List.sum_cons]
      have := hch.length
      omega
    · intro J hJ
      rcases List.mem_append.1 hJ with h | h
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
        have hXR := hch.sub X hX
        refine ⟨hXR, ?_⟩
        have hT : (patsOf X Y (J₀ X).pat).card ≤ l.length ^ X.card := by
          apply patsOf_card_le_list
          intro j hj i hi
          obtain ⟨v, vs, hvl, _, he⟩ := hsp i (hXR hi) j hj
          simp only [J₀, he, List.headD_cons]
          exact hvl
        have hpos : 0 < l.length := List.length_pos_iff.2 (hne l List.mem_cons_self)
        have hXs := hch.card X hX
        calc (J₀ X).cost L Y = (patsOf X Y (J₀ X).pat).card * (2 * X.card * L) := rfl
          _ ≤ l.length ^ sOf l.length * (2 * sOf l.length * L) :=
            Nat.mul_le_mul (hT.trans (Nat.pow_le_pow_right hpos hXs))
              (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hXs))
          _ ≤ Cslot := hC _ hm
      · exact h2 J h
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

theorem jobs_length_le (A S : ℕ) (hA : A ≤ S / 2) (sOf : ℕ → ℕ) (ls : List (List Tmpl)) :
    (ls.map fun l => A / sOf l.length + 1).sum ≤ exactRounds S sOf (ls.map List.length) := by
  induction ls with
  | nil => simp [exactRounds]
  | cons l t ih =>
    simp only [exactRounds, List.map_cons, List.sum_cons] at ih ⊢
    have := Nat.div_le_div_right (c := sOf l.length) hA
    omega

theorem prod_reverse_inv {β G : Type*} [Group G] (f : β → G) (l : List β) :
    (l.reverse.map fun J => (f J)⁻¹).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, ih]
    simp

/-! ### A program -/

/-- **The action of a program.** The rows of `QO` see the product of the `eT` along their values, and
the rows of `QE` see its inverse. The mirror orbits get the same with `eM`. -/
theorem program_main (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ → ℕ)
    (hs : ∀ m ∈ ls.map List.length, 0 < sOf m) (Cslot : ℕ)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) (S : ℕ)
    {QO QE Y : Finset (Fin n)} (c : PairCtx (QO ∪ QE) Y) (hd : Disjoint QO QE)
    (hcO : QO.card ≤ S / 2) (hcE : QE.card ≤ S / 2) (vals : Fin n → Fin n → List Tmpl)
    (hv : ∀ i ∈ QO ∪ QE, ∀ j ∈ Y, List.Forall₂ (· ∈ ·) (vals i j) ls) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
      W.length ≤ exactRounds S sOf (ls.map List.length) * (2 * Y.card + 2 * Cslot) ∧
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
  obtain ⟨jsO, o1, o2, o3⟩ := exists_jobs QO Y L Cslot sOf ls vals hne hL hs hC
    (fun i hi j hj => hv i (hO hi) j hj)
  obtain ⟨jsE, e1, e2, e3⟩ := exists_jobs QE Y L Cslot sOf ls vals hne hL hs hC
    (fun i hi j hj => hv i (hE hi) j hj)
  set R := exactRounds S sOf (ls.map List.length) with hR
  obtain ⟨W, w1, w2, w3, w4⟩ := exists_rounds hn c hO hE hd L Cslot R jsO jsE.reverse
    (o1.trans (jobs_length_le _ S hcO sOf ls))
    (by rw [List.length_reverse]; exact e1.trans (jobs_length_le _ S hcE sOf ls))
    o2 (fun J hJ => e2 J (List.mem_reverse.1 hJ))
  refine ⟨W, w1, w2, w3, ?_⟩
  intro i j hi hj
  obtain ⟨A1, A2⟩ := w4 i j hi hj
  have offO : ∀ J ∈ jsO, ¬ (i ∈ QO ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(o2 J hJ).1 h.1, h.2⟩) (fun h => h₂ ⟨(o2 J hJ).1 h.1, h.2⟩)
  have offE : ∀ J ∈ jsE, ¬ (i ∈ QE ∧ j ∈ Y) → ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) →
      J.act L Y i j = 1 := fun J hJ h₁ h₂ => Job.act_off L Y
    (fun h => h₁ ⟨(e2 J hJ).1 h.1, h.2⟩) (fun h => h₂ ⟨(e2 J hJ).1 h.1, h.2⟩)
  by_cases c1 : i ∈ QO ∧ j ∈ Y
  · have hnE : ¬ (i ∈ QE ∧ j ∈ Y) := fun h => Finset.disjoint_left.1 hd c1.1 h.1
    have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c1.2 (hE h.1)
    rw [if_pos c1, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) hnE hnE'), ← o3 eT i j c1.1 c1.2]
    congr 1
    exact List.map_congr_left fun J hJ =>
      Job.act_target c L (((o2 J hJ).1).trans hO) c1.2
  · rw [if_neg c1]
    by_cases c2 : i ∈ QE ∧ j ∈ Y
    · have hnO' : ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) := fun h => c.not_rev_mem c2.2 (hO h.1)
      rw [if_pos c2, A2 (fun J hJ => offO J hJ c1 hnO'), prod_reverse_inv, ← e3 eT i j c2.1 c2.2]
      congr 2
      exact List.map_congr_left fun J hJ =>
        Job.act_target c L (((e2 J hJ).1).trans hE) c2.2
    · rw [if_neg c2]
      by_cases c3 : Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y
      · have hnE' : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) :=
          fun h => Finset.disjoint_left.1 hd c3.1 h.1
        rw [if_pos c3, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) c2 hnE'),
          ← o3 eM _ _ c3.1 c3.2]
        congr 1
        exact List.map_congr_left fun J hJ =>
          Job.act_mirror c L (((o2 J hJ).1).trans hO) c3.2
      · rw [if_neg c3]
        by_cases c4 : Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y
        · rw [if_pos c4, A2 (fun J hJ => offO J hJ c1 c3), prod_reverse_inv,
            ← e3 eM _ _ c4.1 c4.2]
          congr 2
          exact List.map_congr_left fun J hJ =>
            Job.act_mirror c L (((e2 J hJ).1).trans hE) c4.2
        · rw [if_neg c4, A1 (fun J hJ => offE J (List.mem_reverse.1 hJ) c2 c4)]
          apply List.prod_eq_one
          intro x hx
          obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
          exact offO J hJ c1 c3

/-! ### Splitting a block, and solving with universal lists -/

/-- A block of at most `S` rows, `S` even, splits in two halves of at most `S / 2` rows. -/
theorem exists_split (Q : Finset (Fin n)) (S : ℕ) (hS : Even S) (hQ : Q.card ≤ S) :
    ∃ QO QE : Finset (Fin n), QO ∪ QE = Q ∧ Disjoint QO QE ∧ QO.card ≤ S / 2 ∧ QE.card ≤ S / 2 := by
  obtain ⟨a, rfl⟩ := hS
  have ha : (a + a) / 2 = a := by omega
  rw [ha]
  by_cases h : Q.card ≤ a
  · exact ⟨Q, ∅, by simp, by simp, h, by simp⟩
  · obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq (show a ≤ Q.card by omega)
    refine ⟨T, Q \ T, Finset.union_sdiff_of_subset hT, Finset.disjoint_sdiff, hc.le, ?_⟩
    rw [Finset.card_sdiff_of_subset hT, hc]
    omega

/-- **A program solves any even targets on the orbits of a block.** Target and mirror orbit of a pair
get independent targets, thanks to the universal lists. -/
theorem program_solve (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ → ℕ)
    (hs : ∀ m ∈ ls.map List.length, 0 < sOf m) (Cslot : ℕ)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) (S : ℕ) (hS : Even S)
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (hQ : Q.card ≤ S) (π : Fin n → Fin n → Perm (Fin 24))
    (hπ : ∀ i j, Perm.sign (π i j) = 1) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
      W.length ≤ exactRounds S sOf (ls.map List.length) * (2 * Y.card + 2 * Cslot) ∧
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
  obtain ⟨W, w1, w2, w3, w4⟩ := program_main hn ls hne L hL sOf hs Cslot hC S c hd hcO hcE vals
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

end RubiksGN
