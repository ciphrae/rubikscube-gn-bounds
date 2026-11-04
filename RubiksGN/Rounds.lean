import RubiksGN.Pass

/-!
# One round of the exact scheme

A round is a pass of direction `true` over a set `XO` of rows, followed by a pass of direction `false`
over a disjoint set `XE`, on the same columns `Y`. A row of `XO` sees `eT`, a row of `XE` sees `eT⁻¹`, and
every other orbit sees the identity, because a row outside the block of a pass sees the plain column turn.
The values of the two passes may have different types.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ} {α α₁ α₂ : Type*}

/-- The element of a value on the target orbit: the commutator `[h, K]`. -/
def eT (τ : Tmpl) : Perm (Fin 24) := conjT τ true * colK⁻¹

/-- The element of a value on the mirror orbit: the commutator `[h', K']`. -/
def eM (τ : Tmpl) : Perm (Fin 24) := conjM τ true * colM⁻¹

theorem colK_mul_conjT_false (τ : Tmpl) : colK * conjT τ false = (eT τ)⁻¹ := by
  simp [eT, conjT, _root_.mul_assoc]

theorem colM_mul_conjM_false (τ : Tmpl) : colM * conjM τ false = (eM τ)⁻¹ := by
  simp [eM, conjM, _root_.mul_assoc]

theorem PairCtx.mono {Q X Y : Finset (Fin n)} (c : PairCtx Q Y) (h : X ⊆ Q) : PairCtx X Y where
  hX := fun i hi => c.hX i (h hi)
  hY := c.hY
  hXY := fun i hi => c.hXY i (h hi)

/-- Both a member of `Q` and of `Y` cannot be attached to the same index. -/
theorem PairCtx.not_rev_mem {Q Y : Finset (Fin n)} (c : PairCtx Q Y) {j : Fin n} (hj : j ∈ Y) :
    Fin.rev j ∉ Q := fun h => c.hXY _ h j hj (by rw [layerZ_rev]; ring)

theorem PairCtx.not_rev_mem' {Q Y : Finset (Fin n)} (c : PairCtx Q Y) {i : Fin n} (hi : i ∈ Q) :
    Fin.rev i ∉ Y := fun h => c.hXY i hi _ h (by rw [layerZ_rev])

section Round

variable [DecidableEq α] [DecidableEq α₁] [DecidableEq α₂]

/-- A row of `Q` outside the block of the pass sees the plain column turn. -/
theorem pass_off_target (hn : 2 ≤ n) {Q X Y : Finset (Fin n)} (c : PairCtx Q Y) (hX : X ⊆ Q)
    (τ : α → Tmpl) (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hiQ : i ∈ Q) (hiX : i ∉ X)
    (hjY : j ∈ Y) : Rv (rep i j) (passW hn X Y τ pat d) = dpow d colK := by
  have hi := c.hX i hiQ
  have hri := isRow_coord hi
  have hcj := c.hY j hjY
  have hne := c.hXY i hiQ j hjY
  have hG : Generic i j := ⟨hri.1, hri.2, hcj.1, hcj.2, hne⟩
  have hj : IsCol j := by
    simp only [IsCol]
    simp only [layerZ] at hcj
    omega
  rw [pass_single _ hn X Y τ pat d hjY]
  · rw [Rv_gW_clear hn X τ _ i j]
    · simp [colT, rvL_col_target hG]
    · intro i' hi'
      refine clear_row (c.hX i' (hX hi')) hi hj (fun he => hiX (he ▸ hi')) ?_
      rintro rfl
      exact c.not_rev_mem hjY (hX hi')
  · intro j' hj' hne'
    apply rvL_col_clear
    refine clear_col c hi hj hj' hne' ?_
    rintro rfl
    exact c.not_rev_mem' hiQ hj'

/-- The mirror analogue of `pass_off_target`. -/
theorem pass_off_mirror (hn : 2 ≤ n) {Q X Y : Finset (Fin n)} (c : PairCtx Q Y) (hX : X ⊆ Q)
    (τ : α → Tmpl) (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hi : IsRow i) (hj : IsCol j)
    (hrjQ : Fin.rev j ∈ Q) (hrjX : Fin.rev j ∉ X) (hri : Fin.rev i ∈ Y) :
    Rv (rep i j) (passW hn X Y τ pat d) = dpow d colM := by
  have a := isRow_coord hi
  have b := isRow_coord (c.hX _ hrjQ)
  have hne := c.hXY _ hrjQ _ hri
  simp only [layerZ_rev] at b hne
  have hG : Generic i j := ⟨a.1, a.2, by omega, by omega, by omega⟩
  rw [pass_single _ hn X Y τ pat d hri]
  · rw [Rv_gW_clear hn X τ _ i j]
    · simp [colT, rvL_col_mirror hG (layerZ_rev i)]
    · intro x hx
      refine clear_row (c.hX x (hX hx)) hi hj ?_ (fun he => hrjX (he ▸ hx))
      rintro rfl
      exact c.hXY _ (hX hx) _ hri (by rw [layerZ_rev])
  · intro j' hj' hne'
    apply rvL_col_clear
    refine clear_col c hi hj hj' ?_ hne'
    rintro rfl
    exact c.not_rev_mem hj' hrjQ

/-- No column of `Y` touches the orbit of a row of `Q` and a column outside `Y`. -/
theorem pass_off_col (hn : 2 ≤ n) {Q X Y : Finset (Fin n)} (c : PairCtx Q Y) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hj : IsCol j) (hiQ : i ∈ Q) (hjY : j ∉ Y) :
    Rv (rep i j) (passW hn X Y τ pat d) = 1 := by
  apply pass_trivial
  intro j' hj'
  apply rvL_col_clear
  refine clear_col c (c.hX i hiQ) hj hj' (fun he => hjY (he ▸ hj')) ?_
  rintro rfl
  exact c.not_rev_mem' hiQ hj'

/-- No column of `Y` touches the mirror orbit when the row is outside `Y`. -/
theorem pass_off_col' (hn : 2 ≤ n) {Q X Y : Finset (Fin n)} (c : PairCtx Q Y) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hi : IsRow i) (hj : IsCol j)
    (hrjQ : Fin.rev j ∈ Q) (hri : Fin.rev i ∉ Y) :
    Rv (rep i j) (passW hn X Y τ pat d) = 1 := by
  apply pass_trivial
  intro j' hj'
  apply rvL_col_clear
  refine clear_col c hi hj hj' ?_ (fun he => hri (he ▸ hj'))
  rintro rfl
  exact c.not_rev_mem hj' hrjQ

/-- One round: a pass of direction `true` on `XO`, a pass of direction `false` on `XE`. -/
noncomputable def roundW (hn : 2 ≤ n) (XO XE Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) : Word n :=
  passW hn XO Y τ₁ pat₁ true ++ passW hn XE Y τ₂ pat₂ false

theorem roundW_isQ (hn : 2 ≤ n) (XO XE Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) :
    ∀ m ∈ roundW hn XO XE Y τ₁ τ₂ pat₁ pat₂, IsQ m := by
  intro m hm
  rcases List.mem_append.1 hm with h | h
  · exact passW_isQ hn XO Y τ₁ pat₁ _ m h
  · exact passW_isQ hn XE Y τ₂ pat₂ _ m h

/-- The length of a round. -/
theorem roundW_length_le (hn : 2 ≤ n) (XO XE Y : Finset (Fin n)) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) (L : ℕ)
    (hL₁ : ∀ a, tmplLen (τ₁ a) ≤ L) (hL₂ : ∀ a, tmplLen (τ₂ a) ≤ L) :
    (roundW hn XO XE Y τ₁ τ₂ pat₁ pat₂).length ≤ 2 * Y.card +
      ((patsOf XO Y pat₁).card * (2 * XO.card * L) + (patsOf XE Y pat₂).card * (2 * XE.card * L)) := by
  have h1 := passW_length_le hn XO Y τ₁ pat₁ true L hL₁
  have h2 := passW_length_le hn XE Y τ₂ pat₂ false L hL₂
  simp only [roundW, List.length_append]
  omega

/-- **The action of a round on all orbits of rows and columns.** -/
theorem round_Rv (hn : 2 ≤ n) {Q XO XE Y : Finset (Fin n)} (c : PairCtx Q Y) (hO : XO ⊆ Q)
    (hE : XE ⊆ Q) (hd : Disjoint XO XE) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) {i j : Fin n} (hi : IsRow i)
    (hj : IsCol j) :
    Rv (rep i j) (roundW hn XO XE Y τ₁ τ₂ pat₁ pat₂) =
      if i ∈ XO ∧ j ∈ Y then eT (τ₁ (pat₁ j i))
      else if i ∈ XE ∧ j ∈ Y then (eT (τ₂ (pat₂ j i)))⁻¹
      else if Fin.rev j ∈ XO ∧ Fin.rev i ∈ Y then eM (τ₁ (pat₁ (Fin.rev i) (Fin.rev j)))
      else if Fin.rev j ∈ XE ∧ Fin.rev i ∈ Y then (eM (τ₂ (pat₂ (Fin.rev i) (Fin.rev j))))⁻¹
      else 1 := by
  have cO := c.mono hO
  have cE := c.mono hE
  rw [roundW, Rv_append]
  by_cases hiQ : i ∈ Q
  · have hri : Fin.rev i ∉ Y := c.not_rev_mem' hiQ
    by_cases hjY : j ∈ Y
    · by_cases hiO : i ∈ XO
      · have hiE : i ∉ XE := Finset.disjoint_left.1 hd hiO
        rw [if_pos ⟨hiO, hjY⟩, pass_target hn cO τ₁ pat₁ true hiO hjY,
          pass_off_target hn c hE τ₂ pat₂ false hiQ hiE hjY]
        rfl
      · rw [if_neg (fun h => hiO h.1)]
        by_cases hiE : i ∈ XE
        · rw [if_pos ⟨hiE, hjY⟩, pass_off_target hn c hO τ₁ pat₁ true hiQ hiO hjY,
            pass_target hn cE τ₂ pat₂ false hiE hjY]
          exact colK_mul_conjT_false _
        · rw [if_neg (fun h => hiE h.1), if_neg (fun h => hri h.2), if_neg (fun h => hri h.2),
            pass_off_target hn c hO τ₁ pat₁ true hiQ hiO hjY,
            pass_off_target hn c hE τ₂ pat₂ false hiQ hiE hjY]
          simp
    · rw [if_neg (fun h => hjY h.2), if_neg (fun h => hjY h.2), if_neg (fun h => hri h.2),
        if_neg (fun h => hri h.2), pass_off_col hn c τ₁ pat₁ true hj hiQ hjY,
        pass_off_col hn c τ₂ pat₂ false hj hiQ hjY, one_mul]
  · rw [if_neg (fun h => hiQ (hO h.1)), if_neg (fun h => hiQ (hE h.1))]
    by_cases hrjQ : Fin.rev j ∈ Q
    · by_cases hri : Fin.rev i ∈ Y
      · by_cases hrjO : Fin.rev j ∈ XO
        · have hrjE : Fin.rev j ∉ XE := Finset.disjoint_left.1 hd hrjO
          rw [if_pos ⟨hrjO, hri⟩, pass_mirror hn cO τ₁ pat₁ true hi hj hrjO hri,
            pass_off_mirror hn c hE τ₂ pat₂ false hi hj hrjQ hrjE hri]
          rfl
        · rw [if_neg (fun h => hrjO h.1)]
          by_cases hrjE : Fin.rev j ∈ XE
          · rw [if_pos ⟨hrjE, hri⟩, pass_off_mirror hn c hO τ₁ pat₁ true hi hj hrjQ hrjO hri,
              pass_mirror hn cE τ₂ pat₂ false hi hj hrjE hri]
            exact colM_mul_conjM_false _
          · rw [if_neg (fun h => hrjE h.1), pass_off_mirror hn c hO τ₁ pat₁ true hi hj hrjQ hrjO hri,
              pass_off_mirror hn c hE τ₂ pat₂ false hi hj hrjQ hrjE hri]
            simp
      · rw [if_neg (fun h => hri h.2), if_neg (fun h => hri h.2),
          pass_off_col' hn c τ₁ pat₁ true hi hj hrjQ hri,
          pass_off_col' hn c τ₂ pat₂ false hi hj hrjQ hri, one_mul]
    · rw [if_neg (fun h => hrjQ (hO h.1)), if_neg (fun h => hrjQ (hE h.1))]
      have hrow : ∀ X : Finset (Fin n), X ⊆ Q → ∀ i' ∈ X,
          Clear n (layerZ n i) (layerZ n j) (layerZ n i') := fun X hX i' hi' =>
        clear_row (c.hX i' (hX hi')) hi hj (fun he => hiQ (he ▸ hX hi'))
          (fun he => hrjQ (he ▸ hX hi'))
      rw [pass_plain _ hn XO Y τ₁ pat₁ true (fun p => Rv_gW_clear hn XO τ₁ p i j (hrow XO hO)),
        pass_plain _ hn XE Y τ₂ pat₂ false (fun p => Rv_gW_clear hn XE τ₂ p i j (hrow XE hE))]
      exact colT_cancel _ true _

/-- A pass fixes the skeleton: its columns miss these orbits. -/
theorem passW_fixesSkel (hn : 2 ≤ n) {X Y : Finset (Fin n)}
    (hY : ∀ j ∈ Y, 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) : FixesSkel hn (passW hn X Y τ pat d) := by
  have key : ∀ i j : Fin n, (∀ j' ∈ Y, Clear n (layerZ n i) (layerZ n j) (layerZ n j')) → ∀ k,
      Word.eval (passW hn X Y τ pat d) (e (rep i j) k) = e (rep i j) k := by
    intro i j h k
    have this : Rv (rep i j) (passW hn X Y τ pat d) = 1 :=
      pass_trivial _ hn X Y τ pat d (fun j' hj' => rvL_col_clear i j j' (h j' hj') d)
    rw [eval_of_Rv _ _ (passW_isQ hn X Y τ pat d) this]
    rfl
  constructor
  · intro j hj k
    apply key
    intro j' hj'
    have a := hY j' hj'
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
    have a := hY j' hj'
    rw [hm]
    simp only [Clear]
    omega

/-- A round fixes the skeleton. -/
theorem roundW_fixesSkel (hn : 2 ≤ n) {XO XE Y : Finset (Fin n)}
    (hY : ∀ j ∈ Y, 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1) (τ₁ : α₁ → Tmpl) (τ₂ : α₂ → Tmpl)
    (pat₁ : Fin n → Fin n → α₁) (pat₂ : Fin n → Fin n → α₂) :
    FixesSkel hn (roundW hn XO XE Y τ₁ τ₂ pat₁ pat₂) :=
  (passW_fixesSkel hn hY τ₁ pat₁ true).append (passW_fixesSkel hn hY τ₂ pat₂ false)

end Round

end RubiksGN
