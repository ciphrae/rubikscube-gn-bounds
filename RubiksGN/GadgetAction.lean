import RubiksGN.Gadget

/-!
# The exact action of the rectangle commutator on stickers

Stickers are addressed by orbit coordinates: `e (rep i j) k` is the image under the rotation `k` of
the sticker `(layerZ i, layerZ j, n)` on the top face.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-- Quarter turn about the `x` axis in direction `d`. -/
def rxd (d : Bool) : Fin 24 := if d then rx .x else inv (rx .x)

/-- The inverse of the quarter turn about the `z` axis. -/
def rzi : Fin 24 := inv (rx .z)

theorem act_rzi (x y z : ℤ) : act rzi (x, y, z) = (y, -x, z) := rfl
theorem act_rxd_true (x y z : ℤ) : act (rxd true) (x, y, z) = (x, -z, y) := rfl
theorem act_rxd_false (x y z : ℤ) : act (rxd false) (x, y, z) = (x, z, -y) := rfl
theorem act_rz (x y z : ℤ) : act (rx .z) (x, y, z) = (-y, x, z) := rfl

/-- All layers of `S` about the `x` axis, in direction `d`. -/
noncomputable def sl (d : Bool) (S : ℤ → Prop) : Perm (Sticker n) :=
  if d then slice n .x S else (slice n .x S)⁻¹

theorem sl_of (d : Bool) (S : ℤ → Prop) (q : Sticker n) (h : S (clamp n q.1.1)) :
    sl d S q = actPerm n (rxd d) q := by
  cases d
  · simp only [sl, rxd, Bool.false_eq_true, if_false]
    rw [slice_inv_apply_of n .x S q h, actPerm_inv]
  · simp only [sl, rxd, if_true]
    exact slice_apply_of n .x S q h

theorem sl_not (d : Bool) (S : ℤ → Prop) (q : Sticker n) (h : ¬ S (clamp n q.1.1)) :
    sl d S q = q := by
  cases d
  · simp only [sl, Bool.false_eq_true, if_false]
    exact slice_inv_apply_not n .x S q h
  · simp only [sl, if_true]
    exact slice_apply_not n .x S q h

theorem sl_inv (d : Bool) (S : ℤ → Prop) : (sl d S : Perm (Sticker n))⁻¹ = sl (!d) S := by
  cases d <;> simp [sl]

/-- The top layer. -/
noncomputable def Uop (n : ℕ) : Perm (Sticker n) := slice n .z (· = (n : ℤ) - 1)

/-- The conjugated column turn. -/
noncomputable def bOp (d : Bool) (S : ℤ → Prop) : Perm (Sticker n) :=
  Uop n * sl d S * (Uop n)⁻¹

/-- The base commutator. -/
noncomputable def baseC (da db : Bool) (SX SY : ℤ → Prop) : Perm (Sticker n) :=
  sl da SX * bOp db SY * (sl da SX)⁻¹ * (bOp db SY)⁻¹

/-- The support of the conjugated column turn. -/
def Pb (SY : ℤ → Prop) (q : Sticker n) : Prop :=
  SY (clamp n ((Uop n)⁻¹ q).1.1)

theorem Uop_inv_val (q : Sticker n) :
    ((Uop n)⁻¹ q).1 = if clamp n q.1.2.2 = (n : ℤ) - 1 then act rzi q.1 else q.1 := by
  split_ifs with h
  · rw [Uop, slice_inv_apply_of n .z _ q h]; rfl
  · rw [Uop, slice_inv_apply_not n .z _ q h]

theorem Uop_val (q : Sticker n) :
    (Uop n q).1 = if clamp n q.1.2.2 = (n : ℤ) - 1 then act (rx .z) q.1 else q.1 := by
  split_ifs with h
  · rw [Uop, slice_apply_of n .z _ q h]; rfl
  · rw [Uop, slice_apply_not n .z _ q h]

theorem Pb_iff (SY : ℤ → Prop) (x y z : ℤ) (h : IsSticker n (x, y, z)) :
    Pb SY (⟨(x, y, z), h⟩ : Sticker n) ↔
      if clamp n z = (n : ℤ) - 1 then SY (clamp n y) else SY (clamp n x) := by
  simp only [Pb, Uop_inv_val]
  split_ifs <;> rfl

/-- Hypotheses on the sets of row and column layers. -/
structure RectData (n : ℕ) (SX SY : ℤ → Prop) : Prop where
  hn : 2 ≤ n
  hX : ∀ l, SX l → -((n : ℤ) - 1) < l ∧ l < 0
  hY : ∀ l, SY l → 0 ≤ l

variable {SX SY : ℤ → Prop}

theorem Uop_fix_of (q : Sticker n) (h : ¬ clamp n q.1.2.2 = (n : ℤ) - 1) : Uop n q = q :=
  slice_apply_not n .z _ q h

/-- The support of the commutator's overlap. -/
def InZ (SX SY : ℤ → Prop) (z : Sticker n) : Prop := SX (clamp n z.1.1) ∧ Pb SY z

theorem clamp_of_ne (t : ℤ) (h1 : t ≠ n) (h2 : t ≠ -(n : ℤ)) : clamp n t = t := by
  simp [clamp, h1, h2]

theorem not_top (t : ℤ) (h1 : t < (n : ℤ) - 1) (h2 : -(n : ℤ) < t) : ¬ clamp n t = (n : ℤ) - 1 := by
  rw [clamp_of_ne t (by omega) (by omega)]; omega

theorem inZ_forms (d : RectData n SX SY) (z : Sticker n) (hz : InZ SX SY z) :
    (∃ x y, SX x ∧ SY y ∧ IsCoord n x ∧ IsCoord n y ∧ z.1 = (x, y, (n : ℤ))) ∨
    (∃ x, SX x ∧ SY ((n : ℤ) - 1) ∧ IsCoord n x ∧ z.1 = (x, (n : ℤ), (n : ℤ) - 1)) := by
  obtain ⟨⟨x, y, z'⟩, hs⟩ := z
  obtain ⟨hA, hB⟩ := hz
  rw [Pb_iff] at hB
  simp only at hA
  have hn := d.hn
  have hx := d.hX _ hA
  have hxn : x ≠ n ∧ x ≠ -(n : ℤ) := by
    simp only [clamp] at hx
    constructor <;> intro h <;> subst h <;> simp at hx <;> omega
  rw [clamp_of_ne x hxn.1 hxn.2] at hA hx
  simp only [IsSticker, IsCoord] at hs
  split_ifs at hB with htop
  · have hz' : z' = n ∨ z' = (n : ℤ) - 1 := by
      simp only [clamp] at htop
      split_ifs at htop <;> omega
    rcases hz' with rfl | rfl
    · left
      have hyc : IsCoord n y ∧ IsCoord n x := by simp only [IsCoord]; omega
      have : clamp n y = y := clamp_of_ne y (by omega) (by omega)
      rw [this] at hB
      exact ⟨x, y, hA, hB, hyc.2, hyc.1, rfl⟩
    · right
      have hy : y = n ∨ y = -(n : ℤ) := by omega
      rcases hy with rfl | rfl
      · have : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
        rw [this] at hB
        exact ⟨x, hA, hB, by simp only [IsCoord]; omega, rfl⟩
      · have : clamp n (-(n : ℤ)) = -((n : ℤ) - 1) := by simp [clamp]; omega
        rw [this] at hB
        have := d.hY _ hB
        omega
  · rw [clamp_of_ne x hxn.1 hxn.2] at hB
    have := d.hY _ hB
    omega

theorem bOp_form (d' : Bool) (q : Sticker n)
    (htop : clamp n q.1.2.2 = (n : ℤ) - 1) (hS : SY (clamp n (act rzi q.1).1))
    (hnt : ¬ clamp n (act (rxd d') (act rzi q.1)).2.2 = (n : ℤ) - 1) :
    bOp d' SY q = actPerm n (mul (rxd d') rzi) q := by
  have hU : (Uop n)⁻¹ q = actPerm n rzi q := by
    apply Subtype.ext
    rw [Uop_inv_val, if_pos htop]; rfl
  simp only [bOp, Perm.mul_apply]
  rw [hU, sl_of d' SY _ hS, Uop_fix_of _ hnt, actPerm_mul]
  rfl

theorem bOp_inv (d' : Bool) (S : ℤ → Prop) : (bOp d' S : Perm (Sticker n))⁻¹ = bOp (!d') S := by
  simp only [bOp, mul_inv_rev, inv_inv, sl_inv, _root_.mul_assoc]

/-- The values of the commutator's factors at a point of the overlap. -/
theorem inZ_values (d : RectData n SX SY) (da db : Bool) (z : Sticker n) (hz : InZ SX SY z) :
    sl da SX z = actPerm n (rxd da) z ∧
    bOp db SY z = actPerm n (mul (rxd db) rzi) z ∧
    ¬ SX (clamp n (bOp db SY z).1.1) ∧
    ¬ Pb SY (sl da SX z) := by
  have hn := d.hn
  have hYneg : ∀ l, l < 0 → ¬ SY l := fun l hl h => by have := d.hY l h; omega
  have hXpos : ∀ l, 0 ≤ l → ¬ SX l := fun l hl h => by have := d.hX l h; omega
  have ha : sl da SX z = actPerm n (rxd da) z := sl_of da SX z hz.1
  have hb : bOp db SY z = actPerm n (mul (rxd db) rzi) z := by
    rcases inZ_forms d z hz with ⟨x, y, hx, hy, hcx, hcy, hv⟩ | ⟨x, hx, hy, hcx, hv⟩
    · have hxb := d.hX x hx
      apply bOp_form
      · rw [hv]; simp [clamp]
      · rw [hv, act_rzi]
        simp only [IsCoord] at hcy
        rw [clamp_of_ne y (by omega) (by omega)]; exact hy
      · rw [hv, act_rzi]
        cases db
        · rw [act_rxd_false]; simp only
          exact not_top _ (by omega) (by omega)
        · rw [act_rxd_true]; simp only
          exact not_top _ (by omega) (by omega)
    · have hxb := d.hX x hx
      apply bOp_form
      · rw [hv]; simp only [clamp]; split_ifs <;> omega
      · rw [hv, act_rzi]
        have : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
        simpa only [this] using hy
      · rw [hv, act_rzi]
        cases db
        · rw [act_rxd_false]; simp only
          exact not_top _ (by omega) (by omega)
        · rw [act_rxd_true]; simp only
          exact not_top _ (by omega) (by omega)
  refine ⟨ha, hb, ?_, ?_⟩
  · rw [hb, actPerm_val, act_mul]
    rcases inZ_forms d z hz with ⟨x, y, hx, hy, hcx, hcy, hv⟩ | ⟨x, hx, hy, hcx, hv⟩
    · rw [hv, act_rzi]
      have hy0 := d.hY y hy
      simp only [IsCoord] at hcy
      cases db
      · rw [act_rxd_false]; simp only
        rw [clamp_of_ne y (by omega) (by omega)]; exact hXpos _ hy0
      · rw [act_rxd_true]; simp only
        rw [clamp_of_ne y (by omega) (by omega)]; exact hXpos _ hy0
    · rw [hv, act_rzi]
      have : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
      cases db
      · rw [act_rxd_false]; simp only
        rw [this]; exact hXpos _ (by omega)
      · rw [act_rxd_true]; simp only
        rw [this]; exact hXpos _ (by omega)
  · rw [ha]
    rcases inZ_forms d z hz with ⟨x, y, hx, hy, hcx, hcy, hv⟩ | ⟨x, hx, hy, hcx, hv⟩
    · have hxb := d.hX x hx
      have hy0 := d.hY y hy
      simp only [IsCoord] at hcy
      have hz' : z = ⟨(x, y, (n : ℤ)), hv ▸ z.2⟩ := Subtype.ext hv
      rw [hz']
      cases da
      · change ¬ Pb SY (⟨act (rxd false) (x, y, (n : ℤ)), _⟩ : Sticker n)
        simp only [act_rxd_false]
        rw [Pb_iff]
        rw [clamp_of_ne x (by omega) (by omega)]
        rw [if_neg (by rw [clamp_of_ne (-y) (by omega) (by omega)]; omega)]
        exact hYneg _ hxb.2
      · change ¬ Pb SY (⟨act (rxd true) (x, y, (n : ℤ)), _⟩ : Sticker n)
        simp only [act_rxd_true]
        rw [Pb_iff]
        rw [clamp_of_ne x (by omega) (by omega)]
        rw [clamp_of_ne y (by omega) (by omega)]
        have : clamp n (-(n : ℤ)) = -((n : ℤ) - 1) := by simp [clamp]; omega
        rw [this]
        split_ifs
        · exact hYneg _ (by omega)
        · exact hYneg _ hxb.2
    · have hxb := d.hX x hx
      have hz' : z = ⟨(x, (n : ℤ), (n : ℤ) - 1), hv ▸ z.2⟩ := Subtype.ext hv
      rw [hz']
      cases da
      · change ¬ Pb SY (⟨act (rxd false) (x, (n : ℤ), (n : ℤ) - 1), _⟩ : Sticker n)
        simp only [act_rxd_false]
        rw [Pb_iff]
        rw [clamp_of_ne x (by omega) (by omega)]
        have : clamp n (-(n : ℤ)) = -((n : ℤ) - 1) := by simp [clamp]; omega
        rw [this, if_neg (by omega)]
        exact hYneg _ hxb.2
      · change ¬ Pb SY (⟨act (rxd true) (x, (n : ℤ), (n : ℤ) - 1), _⟩ : Sticker n)
        simp only [act_rxd_true]
        rw [Pb_iff]
        have h1 : clamp n (-((n : ℤ) - 1)) = -((n : ℤ) - 1) := clamp_of_ne _ (by omega) (by omega)
        have h2 : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
        rw [h1, h2, if_pos rfl]
        exact hYneg _ (by omega)

theorem sl_fix (da : Bool) (q : Sticker n) (h : ¬ SX (clamp n q.1.1)) : sl da SX q = q :=
  sl_not da SX q h

theorem bOp_fix (db : Bool) (q : Sticker n) (h : ¬ Pb SY q) : bOp db SY q = q := by
  simp only [bOp, Perm.mul_apply]
  rw [sl_not db SY _ h, perm_apply_inv]

theorem clamp_sl (da : Bool) (q : Sticker n) :
    clamp n (sl da SX q).1.1 = clamp n q.1.1 := by
  by_cases h : SX (clamp n q.1.1)
  · rw [sl_of da SX q h]
    cases da
    · have := clamp_act_coord .x ((actPerm n (rx .x))⁻¹ q)
      rw [perm_apply_inv] at this
      exact this.symm
    · exact clamp_act_coord .x q
  · rw [sl_not da SX q h]

theorem Pb_bOp (db : Bool) (q : Sticker n) : Pb SY (bOp db SY q) ↔ Pb SY q := by
  simp only [Pb, bOp, Perm.mul_apply, perm_inv_apply]
  rw [clamp_sl (SX := SY)]

/-- The rotation taking a point of the overlap to the next point of its 3-cycle. -/
def alphaOf (da : Bool) : Fin 24 := rxd da

/-- The rotation taking a point of the overlap to the last point of its 3-cycle. -/
def betaOf (db : Bool) : Fin 24 := mul (rxd db) rzi

theorem baseC_fix (d : RectData n SX SY) (da db : Bool) (q : Sticker n)
    (h : ∀ z, InZ SX SY z → q ≠ z ∧ q ≠ actPerm n (alphaOf da) z ∧ q ≠ actPerm n (betaOf db) z) :
    baseC da db SX SY q = q := by
  refine comm_fix (sl da SX) (bOp db SY) (fun q => SX (clamp n q.1.1)) (Pb SY)
    (fun q hq => sl_fix da q hq) (fun q hq => bOp_fix db q hq)
    (fun q => by rw [clamp_sl]) (fun q => Pb_bOp db q) q ?_ ?_ ?_
  · rintro ⟨h1, h2⟩
    exact (h q ⟨h1, h2⟩).1 rfl
  · intro z h1 h2 he
    have hz : InZ SX SY z := ⟨h1, h2⟩
    rw [(inZ_values d da db z hz).1] at he
    exact (h z hz).2.1 he
  · intro z h1 h2 he
    have hz : InZ SX SY z := ⟨h1, h2⟩
    rw [(inZ_values d da db z hz).2.1] at he
    exact (h z hz).2.2 he

theorem baseC_three (d : RectData n SX SY) (da db : Bool) (z : Sticker n) (hz : InZ SX SY z) :
    baseC da db SX SY z = actPerm n (alphaOf da) z ∧
    baseC da db SX SY (actPerm n (alphaOf da) z) = actPerm n (betaOf db) z ∧
    baseC da db SX SY (actPerm n (betaOf db) z) = z := by
  obtain ⟨h1, h2, h3, h4⟩ := inZ_values d da db z hz
  obtain ⟨h1', h2', h3', h4'⟩ := inZ_values d (!da) (!db) z hz
  have hA : ∀ q : Sticker n, ¬ SX (clamp n q.1.1) → sl da SX q = q := fun q hq => sl_fix da q hq
  have hB : ∀ q : Sticker n, ¬ Pb SY q → bOp db SY q = q := fun q hq => bOp_fix db q hq
  refine ⟨?_, ?_, ?_⟩
  · have := comm_first (sl da SX) (bOp db SY) (fun q => SX (clamp n q.1.1)) hA z
      (by rw [bOp_inv]; exact h3')
    rw [h1] at this
    exact this
  · have := comm_second (sl da SX) (bOp db SY) (fun q => SX (clamp n q.1.1)) (Pb SY) hA hB z h4 h3
    rw [h1, h2] at this
    exact this
  · have := comm_third (sl da SX) (bOp db SY) (Pb SY) hB z (by rw [sl_inv]; exact h4')
    rw [h2] at this
    exact this

end RubiksGN
