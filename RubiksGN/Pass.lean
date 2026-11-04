import RubiksGN.PassAction

/-!
# One pair phase of the "one column move carries `log₂ n` bits" scheme

A *pass* over a block `X` of rows and a set `Y` of columns has one slot per pattern (the restriction to
`X` of the values chosen by a column):
`slot(p) = G(p) · [turn the columns of pattern p] · G(p)⁻¹`. Two passes with opposite directions form a
*pair phase*, acting on the orbit `(i, j)`, `i ∈ X`, `j ∈ Y`, by `c₁ c₂`, and on all other orbits trivially,
provided the mirror orbits are frozen. All the data (templates and patterns) are parameters.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ} {α α₁ α₂ : Type*}

/-! ### Words -/

/-- The conjugator of a slot: the template of the value `p i` on each row `i` of `X`. -/
noncomputable def gW (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) : Word n :=
  X.attach.toList.flatMap fun i => tmplW hn i.1 (τ (p i))

/-- One slot: conjugate, turn the columns `Ys` in direction `d`, and undo. -/
noncomputable def slotW (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α)
    (Ys : List (Fin n)) (d : Bool) : Word n :=
  gW hn X τ p ++ Ys.map (fun j => ((.x, j, dirTurn d) : Move n)) ++ Word.inv (gW hn X τ p)

theorem gW_isQ (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) :
    ∀ m ∈ gW hn X τ p, IsQ m := by
  intro m hm
  obtain ⟨i, _, h⟩ := List.mem_flatMap.1 hm
  exact tmplW_isQ hn _ _ m h

theorem slotW_isQ (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α)
    (Ys : List (Fin n)) (d : Bool) : ∀ m ∈ slotW hn X τ p Ys d, IsQ m := by
  intro m hm
  simp only [slotW, List.mem_append] at hm
  rcases hm with (h | h) | h
  · exact gW_isQ hn X τ p m h
  · obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
    exact isQ_dirTurn _ _ _
  · exact Word.inv_isQ _ (gW_isQ hn X τ p) m h

theorem gW_length_le (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) (L : ℕ)
    (hL : ∀ a, tmplLen (τ a) ≤ L) : (gW hn X τ p).length ≤ X.card * L := by
  have := length_flatMap_le X.attach.toList (fun i => tmplW hn i.1 (τ (p i))) L
    (fun i _ => by rw [tmplW_length]; exact hL _)
  simpa [gW] using this

theorem Rv_gW (v : Sticker n) (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) :
    Rv v (gW hn X τ p) = (X.attach.toList.map fun i => Rv v (tmplW hn i.1 (τ (p i)))).prod :=
  Rv_flatMap v _ _

theorem Rv_slotW (v : Sticker n) (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α)
    (Ys : List (Fin n)) (d : Bool) :
    Rv v (slotW hn X τ p Ys d) =
      Rv v (gW hn X τ p) * (Ys.map (colT v d)).prod * (Rv v (gW hn X τ p))⁻¹ := by
  have h : Rv v (Ys.map fun j => ((.x, j, dirTurn d) : Move n)) = (Ys.map (colT v d)).prod := by
    simp only [Rv, List.map_map]
    rfl
  simp only [slotW, Rv_append, Rv_inv v _ (gW_isQ hn X τ p), h]

/-- The pattern of a column: its values on the rows of `X`. `pat j i` is the value of the entry
`(i, j)`. -/
def patOf (X : Finset (Fin n)) (pat : Fin n → Fin n → α) (j : Fin n) : X → α := fun i => pat j i

section Pass

variable [DecidableEq α]

/-- The patterns occurring among the columns of `Y`. -/
def patsOf (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) : Finset (X → α) :=
  Y.image (patOf X pat)

/-- The columns of a given pattern. -/
noncomputable def colsOf (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) (p : X → α) :
    List (Fin n) :=
  Y.toList.filter fun j => patOf X pat j = p

/-- A pass: one slot per occurring pattern; every column of `Y` is turned exactly once. -/
noncomputable def passW (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) : Word n :=
  (patsOf X Y pat).toList.flatMap fun p => slotW hn X τ p (colsOf X Y pat p) d

theorem patsOf_card_le_cols (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) :
    (patsOf X Y pat).card ≤ Y.card := Finset.card_image_le

theorem patsOf_card_le_pow [Fintype α] (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) :
    (patsOf X Y pat).card ≤ Fintype.card α ^ X.card := by
  calc (patsOf X Y pat).card ≤ Fintype.card (X → α) := Finset.card_le_univ _
    _ = Fintype.card α ^ X.card := by rw [Fintype.card_fun, Fintype.card_coe]

theorem colsOf_nodup (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) (p : X → α) :
    (colsOf X Y pat p).Nodup := (Finset.nodup_toList Y).filter _

theorem perm_cols (X Y : Finset (Fin n)) (pat : Fin n → Fin n → α) :
    ((patsOf X Y pat).toList.flatMap (colsOf X Y pat)).Perm Y.toList := by
  apply perm_flatMap_filter _ (Finset.nodup_toList _) _ (Finset.nodup_toList _)
  intro j hj
  rw [Finset.mem_toList]
  exact Finset.mem_image_of_mem _ (Finset.mem_toList.1 hj)

/-- A pass is made of quarter turns. -/
theorem passW_isQ (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) : ∀ m ∈ passW hn X Y τ pat d, IsQ m := by
  intro m hm
  obtain ⟨p, _, h⟩ := List.mem_flatMap.1 hm
  exact slotW_isQ hn X τ p _ d m h

/-- The length of a pass: `|Y| + T * (2 * |X| * L)`, with `T` the number of occurring patterns. -/
theorem passW_length_le (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) (L : ℕ) (hL : ∀ a, tmplLen (τ a) ≤ L) :
    (passW hn X Y τ pat d).length ≤ Y.card + (patsOf X Y pat).card * (2 * X.card * L) := by
  have key : ∀ P : List (X → α), (P.flatMap fun p => slotW hn X τ p (colsOf X Y pat p) d).length ≤
      (P.flatMap (colsOf X Y pat)).length + P.length * (2 * X.card * L) := by
    intro P
    induction P with
    | nil => simp
    | cons a t ih =>
      have hs : (slotW hn X τ a (colsOf X Y pat a) d).length ≤
          (colsOf X Y pat a).length + 2 * X.card * L := by
        have := gW_length_le hn X τ a L hL
        simp only [slotW, List.length_append, List.length_map, Word.inv_length]
        nlinarith
      rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
        List.length_cons]
      nlinarith
  have h := key (patsOf X Y pat).toList
  rw [(perm_cols X Y pat).length_eq, Finset.length_toList, Finset.length_toList] at h
  exact h

/-! ### The action of a pass on an orbit -/

theorem Rv_passW (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) :
    Rv v (passW hn X Y τ pat d) = ((patsOf X Y pat).toList.map fun p =>
      Rv v (gW hn X τ p) * ((colsOf X Y pat p).map (colT v d)).prod *
        (Rv v (gW hn X τ p))⁻¹).prod := by
  rw [passW, Rv_flatMap]
  simp only [Rv_slotW]

/-- No column of the pass touches the orbit: every slot is `G G⁻¹`. -/
theorem pass_trivial (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) (h : ∀ j ∈ Y, colT v d j = 1) :
    Rv v (passW hn X Y τ pat d) = 1 := by
  rw [Rv_passW]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  have : ((colsOf X Y pat p).map (colT v d)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact h j (Finset.mem_toList.1 (List.mem_filter.1 hj).1)
  rw [this]
  simp

/-- No conjugator acts on the orbit: the slots are plain column turns. -/
theorem pass_plain (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) (h : ∀ p, Rv v (gW hn X τ p) = 1) :
    Rv v (passW hn X Y τ pat d) = (Y.toList.map (colT v d)).prod := by
  rw [Rv_passW]
  simp only [h, one_mul, inv_one, mul_one]
  have e : ∀ P : List (X → α), (P.map fun p => ((colsOf X Y pat p).map (colT v d)).prod).prod =
      ((P.flatMap (colsOf X Y pat)).map (colT v d)).prod := by
    intro P
    induction P with
    | nil => rfl
    | cons a t ih => simp [List.flatMap_cons, ih]
  rw [e]
  apply List.Perm.prod_eq' ((perm_cols X Y pat).map _)
  rw [List.pairwise_map]
  exact List.pairwise_of_forall (fun _ _ => colT_commute v d d _ _)

/-- A single column of the pass touches the orbit: the only nontrivial slot is that of its pattern. -/
theorem pass_single (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {j₀ : Fin n} (hj₀ : j₀ ∈ Y)
    (h : ∀ j ∈ Y, j ≠ j₀ → colT v d j = 1) :
    Rv v (passW hn X Y τ pat d) = Rv v (gW hn X τ (patOf X pat j₀)) * colT v d j₀ *
      (Rv v (gW hn X τ (patOf X pat j₀)))⁻¹ := by
  rw [Rv_passW]
  rw [prod_map_single _ (Finset.nodup_toList _) _ (patOf X pat j₀)
    (Finset.mem_toList.2 (show _ ∈ patsOf X Y pat from Finset.mem_image_of_mem _ hj₀))]
  · rw [prod_map_single _ (colsOf_nodup X Y pat _) _ j₀
      (List.mem_filter.2 ⟨Finset.mem_toList.2 hj₀, by simp⟩)]
    intro j hj hne
    exact h j (Finset.mem_toList.1 (List.mem_filter.1 hj).1) hne
  · intro p _ hne
    have : ((colsOf X Y pat p).map (colT v d)).prod = 1 := by
      apply List.prod_eq_one
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      obtain ⟨hjY, hjp⟩ := List.mem_filter.1 hj
      apply h j (Finset.mem_toList.1 hjY)
      rintro rfl
      exact hne (of_decide_eq_true hjp).symm
    rw [this]
    simp

end Pass

/-! ### The conjugators on the orbits -/

theorem Rv_gW_clear (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) (i j : Fin n)
    (h : ∀ i' ∈ X, Clear n (layerZ n i) (layerZ n j) (layerZ n i')) :
    Rv (rep i j) (gW hn X τ p) = 1 := by
  rw [Rv_gW]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  exact Rv_tmplW_clear hn i j y.1 (h y.1 y.2) _

theorem Rv_gW_target (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α) {i j : Fin n}
    (hiX : i ∈ X) (hG : Generic i j)
    (h : ∀ i' ∈ X, i' ≠ i → Clear n (layerZ n i) (layerZ n j) (layerZ n i')) :
    Rv (rep i j) (gW hn X τ p) = evalT (τ (p ⟨i, hiX⟩)) := by
  rw [Rv_gW, prod_map_single _ (Finset.nodup_toList _) _ ⟨i, hiX⟩
    (Finset.mem_toList.2 (Finset.mem_attach _ _))]
  · exact Rv_tmplW_target hn hG _
  · rintro ⟨x, hx⟩ _ hne
    exact Rv_tmplW_clear hn i j x (h x hx (fun he => hne (Subtype.ext he))) _

theorem Rv_gW_mirror (hn : 2 ≤ n) (X : Finset (Fin n)) (τ : α → Tmpl) (p : X → α)
    {i j i' : Fin n} (hiX : i' ∈ X) (hG : Generic i j) (hi' : layerZ n i' = -layerZ n j)
    (h : ∀ x ∈ X, x ≠ i' → Clear n (layerZ n i) (layerZ n j) (layerZ n x)) :
    Rv (rep i j) (gW hn X τ p) = evalTm (τ (p ⟨i', hiX⟩)) := by
  rw [Rv_gW, prod_map_single _ (Finset.nodup_toList _) _ ⟨i', hiX⟩
    (Finset.mem_toList.2 (Finset.mem_attach _ _))]
  · exact Rv_tmplW_mirror hn hG hi' _
  · rintro ⟨x, hx⟩ _ hne
    exact Rv_tmplW_clear hn i j x (h x hx (fun he => hne (Subtype.ext he))) _

/-! ### The pair phase on one block -/

/-- Hypotheses on the block `X` and the columns `Y`: `X` consists of rows, `Y` of inner nonzero
positive columns, and no index is shared. -/
structure PairCtx (X Y : Finset (Fin n)) : Prop where
  hX : ∀ i ∈ X, IsRow i
  hY : ∀ j ∈ Y, 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1
  hXY : ∀ i ∈ X, ∀ j ∈ Y, layerZ n j ≠ -layerZ n i

theorem isRow_coord {i : Fin n} (hi : IsRow i) :
    layerZ n i < 0 ∧ -((n : ℤ) - 1) < layerZ n i := by
  simp only [IsRow] at hi
  simp only [layerZ]
  omega

theorem isCol_coord {j : Fin n} (hj : IsCol j) : 0 ≤ layerZ n j := by
  simp only [IsCol] at hj
  simp only [layerZ]
  omega

theorem clear_col {X Y : Finset (Fin n)} (c : PairCtx X Y) {i j j' : Fin n} (hi : IsRow i)
    (hj : IsCol j) (hj' : j' ∈ Y) (h1 : j' ≠ j) (h2 : j' ≠ Fin.rev i) :
    Clear n (layerZ n i) (layerZ n j) (layerZ n j') := by
  have a := isRow_coord hi
  have b := isCol_coord hj
  have d := c.hY j' hj'
  have e1 : layerZ n j' ≠ layerZ n j := fun h => h1 (layerZ_inj _ _ h)
  have e2 : layerZ n j' ≠ -layerZ n i := fun h => h2 (layerZ_inj _ _ (by rw [layerZ_rev]; exact h))
  simp only [Clear]
  omega

theorem clear_row {i j i' : Fin n} (hx : IsRow i') (hi : IsRow i) (hj : IsCol j) (h1 : i' ≠ i)
    (h2 : i' ≠ Fin.rev j) : Clear n (layerZ n i) (layerZ n j) (layerZ n i') := by
  have a := isRow_coord hi
  have b := isCol_coord hj
  have d := isRow_coord hx
  have e1 : layerZ n i' ≠ layerZ n i := fun h => h1 (layerZ_inj _ _ h)
  have e2 : layerZ n i' ≠ -layerZ n j := fun h => h2 (layerZ_inj _ _ (by rw [layerZ_rev]; exact h))
  simp only [Clear]
  omega

section Pair

variable [DecidableEq α] [DecidableEq α₁] [DecidableEq α₂]

/-- The pass on a target orbit. -/
theorem pass_target (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hiX : i ∈ X) (hjY : j ∈ Y) :
    Rv (rep i j) (passW hn X Y τ pat d) = conjT (τ (pat j i)) d := by
  have hi := c.hX i hiX
  have hri := isRow_coord hi
  have hcj := c.hY j hjY
  have hne := c.hXY i hiX j hjY
  have hG : Generic i j := ⟨hri.1, hri.2, hcj.1, hcj.2, hne⟩
  have hj : IsCol j := by
    simp only [IsCol]
    simp only [layerZ] at hcj
    omega
  rw [pass_single _ hn X Y τ pat d hjY]
  · rw [Rv_gW_target hn X τ _ hiX hG]
    · simp only [colT, rvL_col_target hG, conjT, patOf]
    · intro i' hi' hne'
      refine clear_row (c.hX i' hi') hi hj hne' ?_
      rintro rfl
      exact c.hXY _ hi' j hjY (by rw [layerZ_rev]; ring)
  · intro j' hj' hne'
    apply rvL_col_clear
    refine clear_col c hi hj hj' hne' ?_
    rintro rfl
    exact c.hXY i hiX _ hj' (by rw [layerZ_rev])

/-- The pass on a mirror orbit: the row `Fin.rev j` is in `X`, and the column `Fin.rev i` in `Y`. -/
theorem pass_mirror (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hi : IsRow i) (hj : IsCol j)
    (hrj : Fin.rev j ∈ X) (hri : Fin.rev i ∈ Y) :
    Rv (rep i j) (passW hn X Y τ pat d) = conjM (τ (pat (Fin.rev i) (Fin.rev j))) d := by
  have a := isRow_coord hi
  have b := isRow_coord (c.hX _ hrj)
  have hne := c.hXY _ hrj _ hri
  simp only [layerZ_rev] at b hne
  have hG : Generic i j := ⟨a.1, a.2, by omega, by omega, by omega⟩
  rw [pass_single _ hn X Y τ pat d hri]
  · rw [Rv_gW_mirror hn X τ _ hrj hG (layerZ_rev j)]
    · simp only [colT, rvL_col_mirror hG (layerZ_rev i), conjM, patOf]
    · intro x hx hne'
      refine clear_row (c.hX x hx) hi hj ?_ hne'
      rintro rfl
      exact c.hXY _ hx _ hri (by rw [layerZ_rev])
  · intro j' hj' hne'
    apply rvL_col_clear
    refine clear_col c hi hj hj' ?_ hne'
    rintro rfl
    exact c.hXY _ hrj _ hj' (by rw [layerZ_rev]; ring)

/-- A pair phase on one block: a pass in direction `d`, then one in direction `!d`. -/
noncomputable def pairW (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool) : Word n :=
  passW hn X Y τ₁ pat₁ d ++ passW hn X Y τ₂ pat₂ (!d)

/-- A pair phase is made of quarter turns. -/
theorem pairW_isQ (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool) :
    ∀ m ∈ pairW hn X Y τ₁ τ₂ pat₁ pat₂ d, IsQ m := by
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact passW_isQ hn X Y τ₁ pat₁ d m h
  · exact passW_isQ hn X Y τ₂ pat₂ _ m h

/-- The length of a pair phase on one block. -/
theorem pairW_length_le (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool) (L : ℕ)
    (hL₁ : ∀ a, tmplLen (τ₁ a) ≤ L) (hL₂ : ∀ a, tmplLen (τ₂ a) ≤ L) :
    (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d).length ≤ 2 * Y.card +
      ((patsOf X Y pat₁).card + (patsOf X Y pat₂).card) * (2 * X.card * L) := by
  have h1 := passW_length_le hn X Y τ₁ pat₁ d L hL₁
  have h2 := passW_length_le hn X Y τ₂ pat₂ (!d) L hL₂
  simp only [pairW, List.length_append]
  nlinarith

/-- **The action of a pair phase on all orbits of rows and columns**, in orbit coordinates. -/
theorem pair_Rv (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ₁ : α₁ → Tmpl)
    (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool)
    (hfreeze : ∀ i ∈ X, ∀ j ∈ Y,
      conjM (τ₁ (pat₁ j i)) d * conjM (τ₂ (pat₂ j i)) (!d) = 1)
    {i j : Fin n} (hi : IsRow i) (hj : IsCol j) :
    Rv (rep i j) (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) =
      if i ∈ X ∧ j ∈ Y then conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d) else 1 := by
  rw [pairW, Rv_append]
  by_cases hiX : i ∈ X
  · by_cases hjY : j ∈ Y
    · rw [if_pos ⟨hiX, hjY⟩, pass_target hn c τ₁ pat₁ d hiX hjY, pass_target hn c τ₂ pat₂ _ hiX hjY]
    · rw [if_neg (fun h => hjY h.2)]
      have hcol : ∀ d' : Bool, ∀ j' ∈ Y, colT (rep i j) d' j' = 1 := by
        intro d' j' hj'
        apply rvL_col_clear
        refine clear_col c hi hj hj' (fun he => hjY (he ▸ hj')) ?_
        rintro rfl
        exact c.hXY i hiX _ hj' (by rw [layerZ_rev])
      rw [pass_trivial _ hn X Y τ₁ pat₁ d (hcol d), pass_trivial _ hn X Y τ₂ pat₂ _ (hcol _), one_mul]
  · rw [if_neg (fun h => hiX h.1)]
    by_cases hrj : Fin.rev j ∈ X
    · by_cases hri : Fin.rev i ∈ Y
      · rw [pass_mirror hn c τ₁ pat₁ d hi hj hrj hri, pass_mirror hn c τ₂ pat₂ _ hi hj hrj hri]
        exact hfreeze _ hrj _ hri
      · have hcol : ∀ d' : Bool, ∀ j' ∈ Y, colT (rep i j) d' j' = 1 := by
          intro d' j' hj'
          apply rvL_col_clear
          refine clear_col c hi hj hj' ?_ (fun he => hri (he ▸ hj'))
          rintro rfl
          exact c.hXY _ hrj _ hj' (by rw [layerZ_rev]; ring)
        rw [pass_trivial _ hn X Y τ₁ pat₁ d (hcol d), pass_trivial _ hn X Y τ₂ pat₂ _ (hcol _),
          one_mul]
    · have hrow : ∀ i' ∈ X, Clear n (layerZ n i) (layerZ n j) (layerZ n i') := by
        intro i' hi'
        exact clear_row (c.hX i' hi') hi hj (fun he => hiX (he ▸ hi')) (fun he => hrj (he ▸ hi'))
      rw [pass_plain _ hn X Y τ₁ pat₁ d (fun p => Rv_gW_clear hn X τ₁ p i j hrow),
        pass_plain _ hn X Y τ₂ pat₂ _ (fun p => Rv_gW_clear hn X τ₂ p i j hrow)]
      exact colT_cancel _ d _

/-- **The action of a pair phase on all orbits of rows and columns.** -/
theorem pair_action (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ₁ : α₁ → Tmpl)
    (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool)
    (hfreeze : ∀ i ∈ X, ∀ j ∈ Y,
      conjM (τ₁ (pat₁ j i)) d * conjM (τ₂ (pat₂ j i)) (!d) = 1)
    {i j : Fin n} (hi : IsRow i) (hj : IsCol j) (k : Fin 24) :
    Word.eval (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) (e (rep i j) k) =
      e (rep i j) (if i ∈ X ∧ j ∈ Y then
        (conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d)) k else k) := by
  rw [eval_of_Rv _ _ (pairW_isQ hn X Y τ₁ τ₂ pat₁ pat₂ d) (pair_Rv hn c τ₁ τ₂ pat₁ pat₂ d hfreeze hi hj)]
  split_ifs <;> rfl

/-- A pair phase fixes the skeleton: all its columns and rows miss these orbits. -/
theorem pairW_fixesSkel (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ₁ : α₁ → Tmpl)
    (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool) :
    FixesSkel hn (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) := by
  have key : ∀ i j : Fin n, (∀ j' ∈ Y, Clear n (layerZ n i) (layerZ n j) (layerZ n j')) → ∀ k,
      Word.eval (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) (e (rep i j) k) = e (rep i j) k := by
    intro i j h k
    have hcol : ∀ d' : Bool, ∀ j' ∈ Y, colT (rep i j) d' j' = 1 :=
      fun d' j' hj' => rvL_col_clear i j j' (h j' hj') d'
    have : Rv (rep i j) (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) = 1 := by
      rw [pairW, Rv_append, pass_trivial _ hn X Y τ₁ pat₁ d (hcol d),
        pass_trivial _ hn X Y τ₂ pat₂ _ (hcol _), one_mul]
    rw [eval_of_Rv _ _ (pairW_isQ hn X Y τ₁ τ₂ pat₁ pat₂ d) this]
    rfl
  constructor
  · intro j hj k
    apply key
    intro j' hj'
    have a := c.hY j' hj'
    have h0 : layerZ n (⟨0, by omega⟩ : Fin n) = -((n : ℤ) - 1) := by simp [layerZ]
    have h1 : layerZ n j = (n : ℤ) - 1 ∨ layerZ n j = 0 := by
      rcases hj with rfl | hj
      · exact Or.inl (layerZ_topI hn)
      · exact Or.inr hj
    rw [h0]
    simp only [Clear]
    omega
  · intro m hm k
    apply key
    intro j' hj'
    have a := c.hY j' hj'
    rw [hm]
    simp only [Clear]
    omega

/-! ### Frozen mirror orbits -/

/-- The mirror freeze, as a decidable statement about the values: any two compatible values of the two
passes net to the identity on the mirror orbit. -/
def Frozen (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (d : Bool) (compat : α₁ → α₂ → Prop) : Prop :=
  ∀ a b, compat a b → conjM (τ₁ a) d * conjM (τ₂ b) (!d) = 1

instance [Fintype α₁] [Fintype α₂] (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (d : Bool)
    (compat : α₁ → α₂ → Prop) [∀ a b, Decidable (compat a b)] :
    Decidable (Frozen τ₁ τ₂ d compat) :=
  inferInstanceAs (Decidable (∀ a b, compat a b → conjM (τ₁ a) d * conjM (τ₂ b) (!d) = 1))

/-- A linear check for `Frozen`, through the frozen 4-cycles `D₁ a`, `D₂ b` of the values: only
`|α₁| + |α₂|` evaluations of templates, instead of `|α₁| |α₂|`. -/
theorem frozen_of_D (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (d : Bool) (compat : α₁ → α₂ → Prop)
    (D₁ : α₁ → Perm (Fin 24)) (D₂ : α₂ → Perm (Fin 24)) (h₁ : ∀ a, conjM (τ₁ a) d = D₁ a)
    (h₂ : ∀ b, conjM (τ₂ b) (!d) = (D₂ b)⁻¹) (hc : ∀ a b, compat a b → D₁ a = D₂ b) :
    Frozen τ₁ τ₂ d compat := by
  intro a b hab
  rw [h₁, h₂, hc a b hab, mul_inv_cancel]

/-- `pair_action` with `Frozen` values and compatible patterns. -/
theorem pair_action_frozen (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ₁ : α₁ → Tmpl)
    (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (d : Bool)
    (compat : α₁ → α₂ → Prop) (hF : Frozen τ₁ τ₂ d compat)
    (hcompat : ∀ i ∈ X, ∀ j ∈ Y, compat (pat₁ j i) (pat₂ j i))
    {i j : Fin n} (hi : IsRow i) (hj : IsCol j) (k : Fin 24) :
    Word.eval (pairW hn X Y τ₁ τ₂ pat₁ pat₂ d) (e (rep i j) k) =
      e (rep i j) (if i ∈ X ∧ j ∈ Y then
        (conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d)) k else k) :=
  pair_action hn c τ₁ τ₂ pat₁ pat₂ d (fun i hi j hj => hF _ _ (hcompat i hi j hj)) hi hj k

/-! ### A whole pair phase: all blocks -/

/-- The columns usable with the block `X`: from `C`, inner, positive, and with no index in `X`. -/
def goodCols (C X : Finset (Fin n)) : Finset (Fin n) :=
  C.filter fun j => 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1 ∧ ∀ i ∈ X, layerZ n j ≠ -layerZ n i

theorem goodCols_ctx (C X : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i) : PairCtx X (goodCols C X) where
  hX := hX
  hY := fun j hj => by
    have := (Finset.mem_filter.1 hj).2
    exact ⟨this.1, this.2.1⟩
  hXY := fun i hi j hj => (Finset.mem_filter.1 hj).2.2.2 i hi

/-- A partition of the rows `R` into at most `|R|/s + 1` blocks of at most `s` rows. -/
structure IsChunking (R : Finset (Fin n)) (s : ℕ) (chunks : List (Finset (Fin n))) : Prop where
  sub : ∀ X ∈ chunks, X ⊆ R
  card : ∀ X ∈ chunks, X.card ≤ s
  disj : chunks.Pairwise Disjoint
  cover : ∀ i ∈ R, ∃ X ∈ chunks, i ∈ X
  length : chunks.length ≤ R.card / s + 1

/-- Every set of rows can be cut into blocks. -/
theorem exists_chunking (s : ℕ) (hs : 0 < s) (R : Finset (Fin n)) :
    ∃ chunks, IsChunking R s chunks := by
  induction' hc : R.card using Nat.strong_induction_on with c ih generalizing R
  by_cases hlt : R.card < s
  · refine ⟨[R], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro X hX
      rw [List.mem_singleton] at hX
      exact hX ▸ subset_rfl
    · intro X hX
      rw [List.mem_singleton] at hX
      exact hX ▸ hlt.le
    · simp
    · intro i hi
      exact ⟨R, by simp, hi⟩
    · simp
  · obtain ⟨T, hTR, hTc⟩ := Finset.exists_subset_card_eq (not_lt.1 hlt)
    have hlt' : (R \ T).card < c := by
      rw [Finset.card_sdiff_of_subset hTR]; omega
    obtain ⟨cs, h⟩ := ih _ hlt' (R \ T) rfl
    refine ⟨T :: cs, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hTR
      · exact (h.sub X hX).trans Finset.sdiff_subset
    · intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hTc.le
      · exact h.card X hX
    · rw [List.pairwise_cons]
      refine ⟨fun X hX => ?_, h.disj⟩
      exact Finset.disjoint_of_subset_right (h.sub X hX) Finset.disjoint_sdiff
    · intro i hi
      by_cases hiT : i ∈ T
      · exact ⟨T, List.mem_cons_self, hiT⟩
      · obtain ⟨X, hX, hiX⟩ := h.cover i (Finset.mem_sdiff.2 ⟨hi, hiT⟩)
        exact ⟨X, List.mem_cons_of_mem _ hX, hiX⟩
    · have h1 := h.length
      rw [Finset.card_sdiff_of_subset hTR, hTc] at h1
      have h2 : R.card / s = (R.card - s) / s + 1 := Nat.div_eq_sub_div hs (not_lt.1 hlt)
      simp only [List.length_cons]
      omega

/-- One whole pair phase: a pair word for each block, on the columns usable with that block. -/
noncomputable def pairPhaseW (hn : 2 ≤ n) (chunks : List (Finset (Fin n))) (C : Finset (Fin n))
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool) : Word n :=
  chunks.flatMap fun X => pairW hn X (goodCols C X) τ₁ τ₂ pat₁ pat₂ d

/-- The pairs served by a pair phase: the row is in a block, and the column is usable with it. -/
def Good (chunks : List (Finset (Fin n))) (C : Finset (Fin n)) (i j : Fin n) : Prop :=
  ∃ X ∈ chunks, i ∈ X ∧ j ∈ goodCols C X

theorem good_iff (chunks : List (Finset (Fin n))) (C : Finset (Fin n)) (i j : Fin n) :
    Good chunks C i j ↔ ∃ X ∈ chunks, i ∈ X ∧ j ∈ C ∧ 0 < layerZ n j ∧
      layerZ n j < (n : ℤ) - 1 ∧ ∀ i' ∈ X, layerZ n j ≠ -layerZ n i' := by
  simp only [Good, goodCols, Finset.mem_filter]

/-- A whole pair phase is made of quarter turns. -/
theorem pairPhaseW_isQ (hn : 2 ≤ n) (chunks : List (Finset (Fin n))) (C : Finset (Fin n))
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool) : ∀ m ∈ pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d, IsQ m := by
  intro m hm
  obtain ⟨X, _, h⟩ := List.mem_flatMap.1 hm
  exact pairW_isQ hn X _ τ₁ τ₂ pat₁ pat₂ d m h

/-- The length of a whole pair phase. -/
theorem pairPhaseW_length_le [Fintype α₁] [Fintype α₂] (hn : 2 ≤ n) {R : Finset (Fin n)} {s : ℕ}
    {chunks : List (Finset (Fin n))} (hc : IsChunking R s chunks) (C : Finset (Fin n))
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool) (L : ℕ) (hL₁ : ∀ a, tmplLen (τ₁ a) ≤ L) (hL₂ : ∀ a, tmplLen (τ₂ a) ≤ L) :
    (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d).length ≤
      (R.card / s + 1) * (2 * C.card +
        (Fintype.card α₁ ^ s + Fintype.card α₂ ^ s) * 2 * s * L) := by
  have hpos₁ : 0 < Fintype.card α₁ :=
    @Fintype.card_pos _ _ ⟨pat₁ ⟨0, by omega⟩ ⟨0, by omega⟩⟩
  have hpos₂ : 0 < Fintype.card α₂ :=
    @Fintype.card_pos _ _ ⟨pat₂ ⟨0, by omega⟩ ⟨0, by omega⟩⟩
  have hone : ∀ X ∈ chunks, (pairW hn X (goodCols C X) τ₁ τ₂ pat₁ pat₂ d).length ≤
      2 * C.card + (Fintype.card α₁ ^ s + Fintype.card α₂ ^ s) * 2 * s * L := by
    intro X hX
    have h1 := pairW_length_le hn X (goodCols C X) τ₁ τ₂ pat₁ pat₂ d L hL₁ hL₂
    have h2 : (goodCols C X).card ≤ C.card := Finset.card_filter_le _ _
    have hXs := hc.card X hX
    have h3 : (patsOf X (goodCols C X) pat₁).card ≤ Fintype.card α₁ ^ s :=
      (patsOf_card_le_pow _ _ _).trans (Nat.pow_le_pow_right hpos₁ hXs)
    have h4 : (patsOf X (goodCols C X) pat₂).card ≤ Fintype.card α₂ ^ s :=
      (patsOf_card_le_pow _ _ _).trans (Nat.pow_le_pow_right hpos₂ hXs)
    have h5 : ((patsOf X (goodCols C X) pat₁).card + (patsOf X (goodCols C X) pat₂).card) *
        (2 * X.card * L) ≤ (Fintype.card α₁ ^ s + Fintype.card α₂ ^ s) * (2 * s * L) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
    calc _ ≤ _ := h1
      _ ≤ 2 * C.card + (Fintype.card α₁ ^ s + Fintype.card α₂ ^ s) * (2 * s * L) := by omega
      _ = _ := by ring
  have h := length_flatMap_le chunks _ _ hone
  exact h.trans (Nat.mul_le_mul_right _ hc.length)

/-- **The action of a whole pair phase**, in orbit coordinates. -/
theorem pairPhase_Rv (hn : 2 ≤ n) (chunks : List (Finset (Fin n))) (C : Finset (Fin n))
    (hrows : ∀ X ∈ chunks, ∀ i ∈ X, IsRow i) (hdisj : chunks.Pairwise Disjoint)
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool)
    (hfreeze : ∀ i j, Good chunks C i j →
      conjM (τ₁ (pat₁ j i)) d * conjM (τ₂ (pat₂ j i)) (!d) = 1)
    {i j : Fin n} (hi : IsRow i) (hj : IsCol j) :
    (Good chunks C i j → Rv (rep i j) (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d) =
      conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d)) ∧
    (¬ Good chunks C i j → Rv (rep i j) (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d) = 1) := by
  induction chunks with
  | nil =>
    refine ⟨fun ⟨X, hX, _⟩ => absurd hX List.not_mem_nil, fun _ => rfl⟩
  | cons X t ih =>
    obtain ⟨hdX, hdt⟩ := List.pairwise_cons.1 hdisj
    have hrt : ∀ X ∈ t, ∀ i ∈ X, IsRow i := fun x hx => hrows x (List.mem_cons_of_mem _ hx)
    have hft : ∀ i j, Good t C i j → conjM (τ₁ (pat₁ j i)) d * conjM (τ₂ (pat₂ j i)) (!d) = 1 := by
      rintro i j ⟨x, hx, h⟩
      exact hfreeze i j ⟨x, List.mem_cons_of_mem _ hx, h⟩
    obtain ⟨ih1, ih2⟩ := ih hrt hdt hft
    have hhead := pair_Rv hn (goodCols_ctx C X (hrows X List.mem_cons_self)) τ₁ τ₂ pat₁ pat₂ d
      (fun i hi j hj => hfreeze i j ⟨X, List.mem_cons_self, hi, hj⟩) hi hj
    have hsplit : Rv (rep i j) (pairPhaseW hn (X :: t) C τ₁ τ₂ pat₁ pat₂ d) =
        Rv (rep i j) (pairW hn X (goodCols C X) τ₁ τ₂ pat₁ pat₂ d) *
          Rv (rep i j) (pairPhaseW hn t C τ₁ τ₂ pat₁ pat₂ d) := by
      simp only [pairPhaseW, List.flatMap_cons, Rv_append]
    rw [hsplit, hhead]
    constructor
    · rintro ⟨x, hx, hix, hjx⟩
      rcases List.mem_cons.1 hx with rfl | hxt
      · have hng : ¬ Good t C i j := by
          rintro ⟨y, hy, hiy, _⟩
          exact Finset.disjoint_left.1 (hdX y hy) hix hiy
        rw [if_pos ⟨hix, hjx⟩, ih2 hng, mul_one]
      · have hnX : i ∉ X := fun hiX => Finset.disjoint_left.1 (hdX x hxt) hiX hix
        rw [if_neg (fun h => hnX h.1), one_mul]
        exact ih1 ⟨x, hxt, hix, hjx⟩
    · intro hng
      have h1 : ¬ (i ∈ X ∧ j ∈ goodCols C X) := fun h => hng ⟨X, List.mem_cons_self, h.1, h.2⟩
      have h2 : ¬ Good t C i j := by
        rintro ⟨x, hx, h⟩
        exact hng ⟨x, List.mem_cons_of_mem _ hx, h⟩
      rw [if_neg h1, ih2 h2, one_mul]

/-- **The action of a whole pair phase.** On good pairs it is `c₁ c₂`, on all other orbits of rows and
columns (including the pairs with a column outside `C`, with a row outside the blocks, with the middle or
the outer column, and with a column of index in the row's own block), it is the identity. -/
theorem pairPhase_action (hn : 2 ≤ n) (chunks : List (Finset (Fin n))) (C : Finset (Fin n))
    (hrows : ∀ X ∈ chunks, ∀ i ∈ X, IsRow i) (hdisj : chunks.Pairwise Disjoint)
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool)
    (hfreeze : ∀ i j, Good chunks C i j →
      conjM (τ₁ (pat₁ j i)) d * conjM (τ₂ (pat₂ j i)) (!d) = 1)
    {i j : Fin n} (hi : IsRow i) (hj : IsCol j) (k : Fin 24) :
    (Good chunks C i j → Word.eval (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d) (e (rep i j) k) =
      e (rep i j) ((conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d)) k)) ∧
    (¬ Good chunks C i j → Word.eval (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d) (e (rep i j) k) =
      e (rep i j) k) := by
  obtain ⟨h1, h2⟩ := pairPhase_Rv hn chunks C hrows hdisj τ₁ τ₂ pat₁ pat₂ d hfreeze hi hj
  have hq := pairPhaseW_isQ hn chunks C τ₁ τ₂ pat₁ pat₂ d
  exact ⟨fun h => eval_of_Rv _ _ hq (h1 h) k, fun h => eval_of_Rv _ _ hq (h2 h) k⟩

/-- A whole pair phase fixes the skeleton. -/
theorem pairPhaseW_fixesSkel (hn : 2 ≤ n) (chunks : List (Finset (Fin n))) (C : Finset (Fin n))
    (hrows : ∀ X ∈ chunks, ∀ i ∈ X, IsRow i)
    (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂)
    (d : Bool) : FixesSkel hn (pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d) := by
  induction chunks with
  | nil => exact FixesSkel.nil hn
  | cons X t ih =>
    exact (pairW_fixesSkel hn (goodCols_ctx C X (hrows X List.mem_cons_self)) τ₁ τ₂ pat₁ pat₂ d).append
      (ih (fun x hx => hrows x (List.mem_cons_of_mem _ hx)))

/-- **One pair phase, all in one statement**, with `Frozen` values and compatible patterns. -/
theorem pairPhase_main [Fintype α₁] [Fintype α₂] (hn : 2 ≤ n) {R : Finset (Fin n)} {s : ℕ}
    {chunks : List (Finset (Fin n))} (hc : IsChunking R s chunks) (hR : ∀ i ∈ R, IsRow i)
    (C : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl) (pat₁ : Fin n → Fin n → α₁)
    (pat₂ : Fin n → Fin n → α₂) (d : Bool) (L : ℕ) (hL₁ : ∀ a, tmplLen (τ₁ a) ≤ L)
    (hL₂ : ∀ a, tmplLen (τ₂ a) ≤ L) (compat : α₁ → α₂ → Prop) (hF : Frozen τ₁ τ₂ d compat)
    (hcompat : ∀ i j, Good chunks C i j → compat (pat₁ j i) (pat₂ j i)) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧
      W.length ≤ (R.card / s + 1) * (2 * C.card +
        (Fintype.card α₁ ^ s + Fintype.card α₂ ^ s) * 2 * s * L) ∧
      FixesSkel hn W ∧
      ∀ i j, IsRow i → IsCol j → ∀ k,
        (Good chunks C i j → Word.eval W (e (rep i j) k) =
          e (rep i j) ((conjT (τ₁ (pat₁ j i)) d * conjT (τ₂ (pat₂ j i)) (!d)) k)) ∧
        (¬ Good chunks C i j → Word.eval W (e (rep i j) k) = e (rep i j) k) := by
  have hrows : ∀ X ∈ chunks, ∀ i ∈ X, IsRow i := fun X hX i hi => hR i (hc.sub X hX hi)
  refine ⟨pairPhaseW hn chunks C τ₁ τ₂ pat₁ pat₂ d, pairPhaseW_isQ hn chunks C τ₁ τ₂ pat₁ pat₂ d,
    pairPhaseW_length_le hn hc C τ₁ τ₂ pat₁ pat₂ d L hL₁ hL₂,
    pairPhaseW_fixesSkel hn chunks C hrows τ₁ τ₂ pat₁ pat₂ d, ?_⟩
  intro i j hi hj k
  exact pairPhase_action hn chunks C hrows hc.disj τ₁ τ₂ pat₁ pat₂ d
    (fun i j hg => hF _ _ (hcompat i j hg)) hi hj k

end Pair

/-- `Frozen` is decidable by evaluation in the kernel. -/
example : Frozen (α₁ := Bool) (α₂ := Bool) (fun _ => []) (fun _ => []) true (fun a b => a = b) := by
  decide +kernel

/-- A nontrivial template. -/
example : conjT [⟨[(.z, true, true)], (.x, false, true)⟩] true =
    evalT [⟨[(.z, true, true)], (.x, false, true)⟩] * colK *
      (evalT [⟨[(.z, true, true)], (.x, false, true)⟩])⁻¹ := by
  decide +kernel

end RubiksGN
