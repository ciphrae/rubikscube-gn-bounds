import RubiksGN.Basic

/-!
# Words, relabelling, and the rectangle commutator

The heart of the upper bound: for a set `X` of "row" layers and a set `Y` of "column" layers, one
commutator of `2|X| + 2|Y| + 4` quarter turns performs a 3-cycle on the sticker orbit of `(x, y)` for
every `(x, y) ∈ X × Y` and moves nothing else (apart from the rigidly attached partner stickers of
wing edges).
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### Words -/

@[simp] theorem Word.eval_nil : Word.eval ([] : Word n) = 1 := rfl

@[simp] theorem Word.eval_cons (m : Move n) (w : Word n) :
    Word.eval (m :: w) = m.toPerm * Word.eval w := by
  simp [Word.eval]

@[simp] theorem Word.eval_append (u v : Word n) :
    Word.eval (u ++ v) = Word.eval u * Word.eval v := by
  simp [Word.eval]

/-- Quarter turns. -/
def IsQ (m : Move n) : Prop := m.2.2 ≠ .half

/-- The opposite turn. -/
def Turn.swap : Turn → Turn
  | .cw => .ccw
  | .half => .half
  | .ccw => .cw

/-- The inverse move. -/
def Move.inv (m : Move n) : Move n := (m.1, m.2.1, m.2.2.swap)

theorem Move.toPerm_inv (m : Move n) (hm : IsQ m) : (Move.inv m).toPerm = m.toPerm⁻¹ := by
  obtain ⟨a, i, t⟩ := m
  cases t
  · simp [Move.inv, Turn.swap, Move.toPerm]
  · exact absurd rfl hm
  · simp [Move.inv, Turn.swap, Move.toPerm]

/-- The inverse word. -/
def Word.inv (w : Word n) : Word n := (w.map Move.inv).reverse

theorem Word.inv_length (w : Word n) : (Word.inv w).length = w.length := by simp [Word.inv]

theorem Word.eval_inv (w : Word n) (hw : ∀ m ∈ w, IsQ m) : Word.eval (Word.inv w) = (Word.eval w)⁻¹ := by
  induction w with
  | nil => simp [Word.inv]
  | cons m t ih =>
    have h1 := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have h2 := Move.toPerm_inv m (hw m List.mem_cons_self)
    simp only [Word.inv, List.map_cons, List.reverse_cons, Word.eval_append, Word.eval_cons,
      Word.eval_nil, mul_one] at *
    rw [h1, h2]; simp

theorem Word.inv_isQ (w : Word n) (hw : ∀ m ∈ w, IsQ m) : ∀ m ∈ Word.inv w, IsQ m := by
  intro m hm
  simp only [Word.inv, List.mem_reverse, List.mem_map] at hm
  obtain ⟨x, hx, rfl⟩ := hm
  have := hw x hx
  obtain ⟨a, i, t⟩ := x
  cases t
  · simp [Move.inv, Turn.swap, IsQ]
  · exact absurd rfl this
  · simp [Move.inv, Turn.swap, IsQ]

/-! ### Elementary facts about layers -/

theorem layerZ_inj (i j : Fin n) (h : layerZ n i = layerZ n j) : i = j := by
  apply Fin.ext
  simp only [layerZ] at h
  omega

theorem layerZ_rev (i : Fin n) : layerZ n (Fin.rev i) = -layerZ n i := by
  have := i.isLt
  simp only [layerZ, Fin.val_rev]
  have h : ((n - (i.val + 1) : ℕ) : ℤ) = (n : ℤ) - (i.val + 1) := by omega
  rw [h]; ring

theorem clamp_neg (t : ℤ) (hn : 0 < n) : clamp n (-t) = -clamp n t := by
  simp only [clamp]
  split_ifs <;> omega

theorem clamp_act_coord (a : Axis) (q : Sticker n) :
    clamp n (a.coord (actPerm n (rx a) q).1) = clamp n (a.coord q.1) := by
  simp [coord_rx]

/-! ### Words for whole slices -/

/-- Turn all layers of a list about one axis. -/
def sliceW (a : Axis) (L : List (Fin n)) (t : Turn) : Word n := L.map fun i => (a, i, t)

theorem sliceW_eval_cw (a : Axis) (L : List (Fin n)) (hL : L.Nodup) :
    Word.eval (sliceW a L .cw) = slice n a (fun l => ∃ i ∈ L, l = layerZ n i) := by
  induction L with
  | nil =>
    ext q : 1
    simp [sliceW, slice_apply_not]
  | cons i t ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.1 hL
    have e := ih ht
    simp only [sliceW, List.map_cons, Word.eval_cons] at e ⊢
    rw [e]
    ext q : 1
    simp only [Perm.mul_apply, Move.toPerm, quarter]
    by_cases hS : ∃ j ∈ t, clamp n (a.coord q.1) = layerZ n j
    · rw [slice_apply_of n a _ q hS, slice_apply_not n a _ _ (by
        rw [clamp_act_coord]
        obtain ⟨j, hj, hjl⟩ := hS
        intro h
        exact hi (layerZ_inj i j (h.symm.trans hjl) ▸ hj))]
      rw [slice_apply_of n a _ q (by
        obtain ⟨j, hj, hjl⟩ := hS
        exact ⟨j, List.mem_cons_of_mem _ hj, hjl⟩)]
    · rw [slice_apply_not n a _ q hS]
      by_cases hi' : clamp n (a.coord q.1) = layerZ n i
      · rw [slice_apply_of n a _ q hi', slice_apply_of n a _ q ⟨i, List.mem_cons_self, hi'⟩]
      · rw [slice_apply_not n a _ q hi', slice_apply_not n a _ q]
        rintro ⟨j, hj, hjl⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact hi' hjl
        · exact hS ⟨j, hj, hjl⟩

theorem sliceW_eval_ccw (a : Axis) (L : List (Fin n)) (hL : L.Nodup) :
    Word.eval (sliceW a L .ccw) = (slice n a (fun l => ∃ i ∈ L, l = layerZ n i))⁻¹ := by
  induction L with
  | nil =>
    ext q : 1
    simp [sliceW, slice_inv_apply_not]
  | cons i t ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.1 hL
    have e := ih ht
    simp only [sliceW, List.map_cons, Word.eval_cons] at e ⊢
    rw [e]
    ext q : 1
    simp only [Perm.mul_apply, Move.toPerm, quarter]
    have hc : clamp n (a.coord ((actPerm n (rx a))⁻¹ q).1) = clamp n (a.coord q.1) := by
      have := clamp_act_coord a ((actPerm n (rx a))⁻¹ q)
      rw [perm_apply_inv] at this
      exact this.symm
    by_cases hS : ∃ j ∈ t, clamp n (a.coord q.1) = layerZ n j
    · rw [slice_inv_apply_of n a _ q hS, slice_inv_apply_not n a _ _ (by
        rw [hc]
        obtain ⟨j, hj, hjl⟩ := hS
        intro h
        exact hi (layerZ_inj i j (h.symm.trans hjl) ▸ hj))]
      rw [slice_inv_apply_of n a _ q (by
        obtain ⟨j, hj, hjl⟩ := hS
        exact ⟨j, List.mem_cons_of_mem _ hj, hjl⟩)]
    · rw [slice_inv_apply_not n a _ q hS]
      by_cases hi' : clamp n (a.coord q.1) = layerZ n i
      · rw [slice_inv_apply_of n a _ q hi', slice_inv_apply_of n a _ q ⟨i, List.mem_cons_self, hi'⟩]
      · rw [slice_inv_apply_not n a _ q hi', slice_inv_apply_not n a _ q]
        rintro ⟨j, hj, hjl⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact hi' hjl
        · exact hS ⟨j, hj, hjl⟩

/-! ### Relabelling a word by a rotation of the whole cube -/

/-- Column of the rotation matrix corresponding to an axis. -/
def Axis.col : Axis → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

/-- The axis onto which `τ` sends `a`. -/
def axImg (τ : Fin 24) (a : Axis) : Axis :=
  if mat τ 0 a.col ≠ 0 then .x else if mat τ 1 a.col ≠ 0 then .y else .z

/-- Whether `τ` preserves the direction of `a`. -/
def axPos (τ : Fin 24) (a : Axis) : Bool :=
  decide (mat τ 0 a.col + mat τ 1 a.col + mat τ 2 a.col = 1)

/-- The rotation corresponding to `rx a` after conjugating with `τ`. -/
def relRot (τ : Fin 24) (a : Axis) : Fin 24 :=
  if axPos τ a then rx (axImg τ a) else inv (rx (axImg τ a))

theorem mul_rx_rel : ∀ (τ : Fin 24) (a : Axis), mul τ (rx a) = mul (relRot τ a) τ := by
  intro τ a
  cases a <;> revert τ <;> decide +kernel

set_option maxHeartbeats 4000000 in
theorem coord_act (τ : Fin 24) (a : Axis) (v : V) :
    (axImg τ a).coord (act τ v) = if axPos τ a then a.coord v else -a.coord v := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨k, hk⟩ := τ
  interval_cases k <;> cases a <;> rfl

/-- Conjugating a slice by a rotation gives a slice (possibly the opposite turn). -/
theorem actPerm_slice (τ : Fin 24) (a : Axis) (S : ℤ → Prop) (hn : 0 < n) (q : Sticker n) :
    actPerm n τ (slice n a S q) =
      (if axPos τ a then slice n (axImg τ a) S
        else (slice n (axImg τ a) (fun l => S (-l)))⁻¹) (actPerm n τ q) := by
  have hrot : actPerm n τ (actPerm n (rx a) q) = actPerm n (relRot τ a) (actPerm n τ q) := by
    apply Subtype.ext
    simp only [actPerm_val, ← act_mul, mul_rx_rel]
  have hc := coord_act τ a q.1
  cases hp : axPos τ a
  · simp only [hp, Bool.false_eq_true, if_false] at hc ⊢
    have hc' : clamp n ((axImg τ a).coord (actPerm n τ q).1) = -clamp n (a.coord q.1) := by
      simp only [actPerm_val]; rw [hc, clamp_neg _ hn]
    have hr : relRot τ a = inv (rx (axImg τ a)) := by simp [relRot, hp]
    by_cases hS : S (clamp n (a.coord q.1))
    · rw [slice_apply_of n a S q hS, slice_inv_apply_of n _ _ _ (by rw [hc', neg_neg]; exact hS),
        hrot, hr, actPerm_inv]
    · rw [slice_apply_not n a S q hS, slice_inv_apply_not n _ _ _ (by rw [hc', neg_neg]; exact hS)]
  · simp only [hp, if_true] at hc ⊢
    have hc' : clamp n ((axImg τ a).coord (actPerm n τ q).1) = clamp n (a.coord q.1) := by
      simp only [actPerm_val]; rw [hc]
    have hr : relRot τ a = rx (axImg τ a) := by simp [relRot, hp]
    by_cases hS : S (clamp n (a.coord q.1))
    · rw [slice_apply_of n a S q hS, slice_apply_of n _ _ _ (by rw [hc']; exact hS), hrot, hr]
    · rw [slice_apply_not n a S q hS, slice_apply_not n _ _ _ (by rw [hc']; exact hS)]

/-- Relabel a move by a rotation of the whole cube. -/
def Move.relabel (τ : Fin 24) (m : Move n) : Move n :=
  if axPos τ m.1 then (axImg τ m.1, m.2.1, m.2.2)
  else (axImg τ m.1, Fin.rev m.2.1, m.2.2.swap)

theorem isQ_relabel (τ : Fin 24) (m : Move n) (hm : IsQ m) : IsQ (Move.relabel τ m) := by
  obtain ⟨a, i, t⟩ := m
  cases t
  · simp only [Move.relabel, IsQ]; split_ifs <;> simp [Turn.swap]
  · exact absurd rfl hm
  · simp only [Move.relabel, IsQ]; split_ifs <;> simp [Turn.swap]

theorem quarter_conj (τ : Fin 24) (a : Axis) (i : Fin n) (hn : 0 < n) (q : Sticker n) :
    actPerm n τ (quarter n a i q) =
      (if axPos τ a then quarter n (axImg τ a) i
        else (quarter n (axImg τ a) (Fin.rev i))⁻¹) (actPerm n τ q) := by
  have h := actPerm_slice τ a (· = layerZ n i) hn q
  have hf : (fun l : ℤ => -l = layerZ n i) = (· = layerZ n (Fin.rev i)) := by
    funext l
    rw [layerZ_rev]
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  simp only [hf] at h
  simpa only [quarter] using h

theorem toPerm_relabel (τ : Fin 24) (m : Move n) (hm : IsQ m) (hn : 0 < n) :
    (Move.relabel τ m).toPerm = actPerm n τ * m.toPerm * (actPerm n τ)⁻¹ := by
  obtain ⟨a, i, t⟩ := m
  ext q : 1
  obtain ⟨r, rfl⟩ := (actPerm n τ).surjective q
  simp only [Perm.mul_apply, perm_inv_apply]
  cases t
  · have h := quarter_conj τ a i hn r
    cases hp : axPos τ a <;> simp only [hp, Bool.false_eq_true, if_false, if_true] at h <;>
      simp only [Move.relabel, hp, Bool.false_eq_true, if_false, if_true, Move.toPerm, Turn.swap] <;>
      rw [h]
  · exact absurd rfl hm
  · have h := quarter_conj τ a i hn ((quarter n a i)⁻¹ r)
    rw [perm_apply_inv] at h
    cases hp : axPos τ a <;> simp only [hp, Bool.false_eq_true, if_false, if_true] at h <;>
      simp only [Move.relabel, hp, Bool.false_eq_true, if_false, if_true, Move.toPerm, Turn.swap]
    · rw [h]; simp
    · rw [h]; simp

theorem eval_relabel (τ : Fin 24) (w : Word n) (hw : ∀ m ∈ w, IsQ m) (hn : 0 < n) :
    Word.eval (w.map (Move.relabel τ)) = actPerm n τ * Word.eval w * (actPerm n τ)⁻¹ := by
  induction w with
  | nil => simp
  | cons m t ih =>
    have h1 := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, Word.eval_cons]
    rw [h1, toPerm_relabel τ m (hw m List.mem_cons_self) hn]
    group

/-! ### The abstract commutator lemma -/

section Comm

variable {α : Type*} (a b : Perm α) (Pa Pb : α → Prop)

theorem comm_fix (ha : ∀ q, ¬ Pa q → a q = q) (hb : ∀ q, ¬ Pb q → b q = q)
    (haI : ∀ q, Pa (a q) ↔ Pa q) (hbI : ∀ q, Pb (b q) ↔ Pb q) (q : α)
    (h1 : ¬ (Pa q ∧ Pb q)) (h2 : ∀ z, Pa z → Pb z → q ≠ a z) (h3 : ∀ z, Pa z → Pb z → q ≠ b z) :
    (a * b * a⁻¹ * b⁻¹) q = q := by
  simp only [Perm.mul_apply]
  by_cases hq : Pb q
  · set r := b⁻¹ q with hr
    have hbr : b r = q := by simp [hr]
    have hPr : Pb r := (hbI r).1 (hbr ▸ hq)
    have hnr : ¬ Pa r := fun h => h3 r h hPr hbr.symm
    have har : a⁻¹ r = r := by
      rw [Perm.inv_eq_iff_eq]; exact (ha r hnr).symm
    rw [har, hbr]
    exact ha q (fun h => h1 ⟨h, hq⟩)
  · have hbq : b⁻¹ q = q := by
      rw [Perm.inv_eq_iff_eq]; exact (hb q hq).symm
    rw [hbq]
    by_cases hp : Pa q
    · set s := a⁻¹ q with hs
      have has : a s = q := by simp [hs]
      have hPs : Pa s := (haI s).1 (has ▸ hp)
      have hns : ¬ Pb s := fun h => h2 s hPs h has.symm
      rw [hb s hns, has]
    · have haq : a⁻¹ q = q := by
        rw [Perm.inv_eq_iff_eq]; exact (ha q hp).symm
      rw [haq, hb q hq, ha q hp]

theorem comm_first (ha : ∀ q, ¬ Pa q → a q = q) (z : α) (h : ¬ Pa (b⁻¹ z)) :
    (a * b * a⁻¹ * b⁻¹) z = a z := by
  simp only [Perm.mul_apply]
  have : a⁻¹ (b⁻¹ z) = b⁻¹ z := by
    rw [Perm.inv_eq_iff_eq]; exact (ha _ h).symm
  rw [this]; simp

theorem comm_second (ha : ∀ q, ¬ Pa q → a q = q) (hb : ∀ q, ¬ Pb q → b q = q) (z : α)
    (h1 : ¬ Pb (a z)) (h2 : ¬ Pa (b z)) :
    (a * b * a⁻¹ * b⁻¹) (a z) = b z := by
  simp only [Perm.mul_apply]
  have : b⁻¹ (a z) = a z := by
    rw [Perm.inv_eq_iff_eq]; exact (hb _ h1).symm
  rw [this, perm_inv_apply, ha _ h2]

theorem comm_third (hb : ∀ q, ¬ Pb q → b q = q) (z : α) (h : ¬ Pb (a⁻¹ z)) :
    (a * b * a⁻¹ * b⁻¹) (b z) = z := by
  simp only [Perm.mul_apply, perm_inv_apply]
  rw [hb _ h]; simp

end Comm

end RubiksGN
