import RubiksGN.Solve

/-!
# Templates and their action on orbit coordinates

A *letter* names a quarter turn relative to a row: an axis, a side and a direction. A *piece* is
`f r f⁻¹`, where `f` is a word of face turns and `r` a single slice of the row's own index. A
*template* is a list of pieces.

On a generic orbit `rep i j` (`layerZ i = -u`, `layerZ j = v`, with `u ≠ v` both inner and nonzero), the
action of every relevant slice on the 24 orbit coordinates does not depend on `n, u, v`: it is read off
the model sticker `vG = (-1, 2, 3)`, where `1, 2, 3` stand for `u, v, n`. All constants of this file are
computable and meant for `decide +kernel`.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### The computable constants -/

/-- The model of a generic orbit: `1, 2, 3` stand for `u, v, n`. -/
def vG : V := (-1, 2, 3)

/-- The layer `c` about the axis `a`, acting on the coordinates of the model orbit. -/
def genP (a : Axis) (c : ℤ) : Perm (Fin 24) :=
  condPerm (lmulP (rx a)) (fun k => a.coord (act k vG) = c) (fun k => by
    change a.coord (act (mul (rx a) k) vG) = c ↔ _
    rw [act_mul, coord_rx])

/-- A permutation or its inverse. -/
def dpow (d : Bool) (g : Perm (Fin 24)) : Perm (Fin 24) := if d then g else g⁻¹

@[simp] theorem dpow_true (g : Perm (Fin 24)) : dpow true g = g := rfl
@[simp] theorem dpow_false (g : Perm (Fin 24)) : dpow false g = g⁻¹ := rfl

theorem dpow_not (d : Bool) (g : Perm (Fin 24)) : dpow (!d) g = (dpow d g)⁻¹ := by
  cases d <;> simp

/-- A letter: axis, side (`true` is the top face, respectively the layer `Fin.rev i` of positive
coordinate) and direction (`true` is `cw`). -/
abbrev TLet := Axis × Bool × Bool

/-- A piece `f r f⁻¹` of a template: a word of face letters and one row letter. -/
structure TPiece where
  f : List TLet
  r : TLet
  deriving DecidableEq, Repr

/-- A template is a list of pieces. -/
abbrev Tmpl := List TPiece

/-- A face letter on a generic orbit. -/
def faceA (l : TLet) : Perm (Fin 24) := dpow l.2.2 (genP l.1 (if l.2.1 then 3 else -3))

/-- A row letter on a generic orbit, for the row of index `u`. -/
def rowT (l : TLet) : Perm (Fin 24) := dpow l.2.2 (genP l.1 (if l.2.1 then 1 else -1))

/-- A row letter on a generic orbit, for the row of index `v` (the mirror case). -/
def rowM (l : TLet) : Perm (Fin 24) := dpow l.2.2 (genP l.1 (if l.2.1 then 2 else -2))

/-- The column `x = +v` on a generic orbit. -/
def colK : Perm (Fin 24) := genP .x 2

/-- The column `x = +u` on a generic orbit (the mirror case). -/
def colM : Perm (Fin 24) := genP .x 1

/-- The value of a word of face letters on a generic orbit. -/
def faceVal (f : List TLet) : Perm (Fin 24) := (f.map faceA).prod

/-- The value of a piece on the target orbit. -/
def pieceT (p : TPiece) : Perm (Fin 24) := faceVal p.f * rowT p.r * (faceVal p.f)⁻¹

/-- The value of a piece on the mirror orbit. -/
def pieceTm (p : TPiece) : Perm (Fin 24) := faceVal p.f * rowM p.r * (faceVal p.f)⁻¹

/-- The value of a template on the target orbit. -/
def evalT (τ : Tmpl) : Perm (Fin 24) := (τ.map pieceT).prod

/-- The value of a template on the mirror orbit. -/
def evalTm (τ : Tmpl) : Perm (Fin 24) := (τ.map pieceTm).prod

/-- A toggled column on the target orbit, conjugated by a template. -/
def conjT (τ : Tmpl) (d : Bool) : Perm (Fin 24) := evalT τ * dpow d colK * (evalT τ)⁻¹

/-- A toggled column on the mirror orbit, conjugated by a template. -/
def conjM (τ : Tmpl) (d : Bool) : Perm (Fin 24) := evalTm τ * dpow d colM * (evalTm τ)⁻¹

/-- The length of the word of a template. -/
def tmplLen (τ : Tmpl) : ℕ := (τ.map fun p => 2 * p.f.length + 1).sum

/-! Sanity checks against `scripts/orbit_model.py`. -/

example : (List.finRange 24).map (fun k => (colK k).val) =
    [0, 1, 2, 3, 4, 13, 6, 7, 8, 9, 10, 11, 12, 21, 14, 15, 16, 17, 18, 5, 20, 19, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (colM k).val) =
    [0, 1, 2, 3, 4, 5, 6, 16, 8, 9, 14, 11, 12, 13, 7, 15, 10, 17, 18, 19, 20, 21, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (rowT (.y, false, true) k).val) =
    [0, 1, 2, 6, 4, 5, 13, 7, 8, 9, 10, 11, 12, 20, 14, 15, 16, 17, 18, 19, 3, 21, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (rowT (.z, true, true) k).val) =
    [0, 1, 8, 3, 4, 2, 6, 7, 12, 9, 10, 11, 5, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (rowM (.y, false, true) k).val) =
    [0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 15, 11, 10, 13, 14, 4, 16, 17, 18, 19, 20, 21, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (rowM (.z, true, true) k).val) =
    [0, 6, 2, 3, 4, 5, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15, 23, 17, 18, 19, 20, 21, 22, 1] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (faceA (.z, true, true) k).val) =
    [3, 1, 2, 10, 4, 5, 6, 7, 8, 9, 19, 11, 12, 13, 14, 15, 16, 17, 18, 0, 20, 21, 22, 23] := by
  decide +kernel
example : (List.finRange 24).map (fun k => (faceA (.z, false, false) k).val) =
    [0, 1, 2, 3, 18, 5, 6, 13, 8, 9, 10, 11, 12, 4, 14, 15, 16, 17, 7, 19, 20, 21, 22, 23] := by
  decide +kernel

/-! ### Which slot of the model a coordinate is -/

set_option maxHeartbeats 4000000 in
/-- Every coordinate of a rotated sticker is a signed slot, and the model tells which one. -/
theorem coord_slot (a : Axis) (k : Fin 24) (x y z : ℤ) :
    (a.coord (act k (x, y, z)) = x ∧ a.coord (act k vG) = -1) ∨
    (a.coord (act k (x, y, z)) = -x ∧ a.coord (act k vG) = 1) ∨
    (a.coord (act k (x, y, z)) = y ∧ a.coord (act k vG) = 2) ∨
    (a.coord (act k (x, y, z)) = -y ∧ a.coord (act k vG) = -2) ∨
    (a.coord (act k (x, y, z)) = z ∧ a.coord (act k vG) = 3) ∨
    (a.coord (act k (x, y, z)) = -z ∧ a.coord (act k vG) = -3) := by
  obtain ⟨k, hk⟩ := k
  interval_cases k <;> cases a <;>
    first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))

/-- The layer corresponding to a slot of the model on the orbit with coordinates `x, y`. -/
def gval (N x y c : ℤ) : ℤ :=
  if c = -1 then x else if c = 1 then -x else if c = 2 then y else if c = -2 then -y
  else if c = 3 then N - 1 else -(N - 1)

/-- The slots. -/
def ValidC (c : ℤ) : Prop := c = -1 ∨ c = 1 ∨ c = 2 ∨ c = -2 ∨ c = 3 ∨ c = -3

theorem clamp_self : clamp n (n : ℤ) = (n : ℤ) - 1 := by
  simp [clamp]

theorem clamp_neg_self (hn : 0 < n) : clamp n (-(n : ℤ)) = -((n : ℤ) - 1) := by
  rw [clamp_neg _ hn, clamp_self]

/-- A generic orbit: both coordinates inner and nonzero, of different absolute value. -/
structure Generic (i j : Fin n) : Prop where
  u0 : layerZ n i < 0
  u1 : -((n : ℤ) - 1) < layerZ n i
  v0 : 0 < layerZ n j
  v1 : layerZ n j < (n : ℤ) - 1
  ne : layerZ n j ≠ -layerZ n i

theorem clamp_coord_slot (i j : Fin n) (a : Axis) (k : Fin 24) :
    clamp n (a.coord (act k (rep i j).1)) =
      gval n (layerZ n i) (layerZ n j) (a.coord (act k vG)) := by
  have hn : 0 < n := i.pos
  have hx := clamp_coord (layerZ_isCoord i)
  have hy := clamp_coord (layerZ_isCoord j)
  have hx' := clamp_coord ((isCoord_neg n _).2 (layerZ_isCoord i))
  have hy' := clamp_coord ((isCoord_neg n _).2 (layerZ_isCoord j))
  change clamp n (a.coord (act k (layerZ n i, layerZ n j, (n : ℤ)))) = _
  rcases coord_slot a k (layerZ n i) (layerZ n j) n with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp only [gval] <;> norm_num <;> first | assumption | exact clamp_self | (rw [clamp_neg_self hn]; ring)

theorem valid_coord (a : Axis) (k : Fin 24) : ValidC (a.coord (act k vG)) := by
  rcases coord_slot a k 0 0 0 with
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [ValidC, h]

theorem gval_inj {i j : Fin n} (hG : Generic i j) {c c' : ℤ} (hc : ValidC c) (hc' : ValidC c')
    (h : gval n (layerZ n i) (layerZ n j) c = gval n (layerZ n i) (layerZ n j) c') : c = c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (simp only [gval] at h; norm_num at h; omega)

/-- On a generic orbit, a layer acts as the model's slot. -/
theorem rvG_generic {i j : Fin n} (hG : Generic i j) (a : Axis) (l : Fin n) {c : ℤ}
    (hc : ValidC c) (hl : layerZ n l = gval n (layerZ n i) (layerZ n j) c) :
    rvG (rep i j) a l = genP a c := by
  apply Equiv.ext
  intro k
  simp only [rvG, genP, condPerm_apply]
  have key : clamp n (a.coord (act k (rep i j).1)) = layerZ n l ↔ a.coord (act k vG) = c := by
    rw [clamp_coord_slot, hl]
    constructor
    · exact fun h => gval_inj hG (valid_coord a k) hc h
    · exact fun h => by rw [h]
  simp only [key]

/-- The layer `l` misses the sticker coordinates `x, y` and is not a face. -/
def Clear (n : ℕ) (x y l : ℤ) : Prop :=
  l ≠ x ∧ l ≠ -x ∧ l ≠ y ∧ l ≠ -y ∧ l ≠ (n : ℤ) - 1 ∧ l ≠ -((n : ℤ) - 1)

theorem Clear.neg {x y l : ℤ} (h : Clear n x y l) : Clear n x y (-l) := by
  simp only [Clear] at h ⊢
  omega

/-- A layer whose absolute coordinate is neither `|x|`, `|y|` nor outer does not touch the orbit. -/
theorem rvG_clear (i j l : Fin n) (h : Clear n (layerZ n i) (layerZ n j) (layerZ n l)) (a : Axis) :
    rvG (rep i j) a l = 1 := by
  apply Equiv.ext
  intro k
  simp only [rvG, condPerm_apply, Perm.one_apply]
  rw [if_neg]
  rw [clamp_coord_slot]
  have hv := valid_coord a k
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases hv with hv | hv | hv | hv | hv | hv <;> rw [hv] <;> simp only [gval] <;> norm_num <;>
    omega

/-! ### Moves on orbit coordinates -/

theorem rvL_dir (v : Sticker n) (a : Axis) (l : Fin n) (d : Bool) :
    rvL v (a, l, dirTurn d) = dpow d (rvG v a l) := by
  cases d <;> simp [rvL, dirTurn, dpow]

theorem rvL_moveInv (v : Sticker n) (m : Move n) (hm : IsQ m) :
    rvL v (Move.inv m) = (rvL v m)⁻¹ := by
  obtain ⟨a, i, t⟩ := m
  cases t
  · simp [rvL, Move.inv, Turn.swap]
  · exact absurd rfl hm
  · simp [rvL, Move.inv, Turn.swap]

@[simp] theorem Rv_nil (v : Sticker n) : Rv v ([] : Word n) = 1 := rfl

@[simp] theorem Rv_cons (v : Sticker n) (m : Move n) (w : Word n) :
    Rv v (m :: w) = rvL v m * Rv v w := by
  simp [Rv]

@[simp] theorem Rv_append (v : Sticker n) (a b : Word n) : Rv v (a ++ b) = Rv v a * Rv v b := by
  simp [Rv]

theorem Rv_inv (v : Sticker n) (w : Word n) (hw : ∀ m ∈ w, IsQ m) :
    Rv v (Word.inv w) = (Rv v w)⁻¹ := by
  induction w with
  | nil => simp [Word.inv]
  | cons m t ih =>
    have h1 := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have h2 := rvL_moveInv v m (hw m List.mem_cons_self)
    simp only [Word.inv, List.map_cons, List.reverse_cons, Rv_append, Rv_cons, Rv_nil, mul_one] at *
    rw [h1, h2]; simp

theorem Rv_flatMap {ι : Type*} (v : Sticker n) (l : List ι) (f : ι → Word n) :
    Rv v (l.flatMap f) = (l.map fun x => Rv v (f x)).prod := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]

theorem eval_of_Rv (v : Sticker n) (w : Word n) (hw : ∀ m ∈ w, IsQ m) {g : Perm (Fin 24)}
    (h : Rv v w = g) (k : Fin 24) : Word.eval w (e v k) = e v (g k) := by
  rw [word_Rv v w hw, h]

/-! ### Words of letters -/

/-- The bottom layer. -/
def botI (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

theorem layerZ_topI (hn : 2 ≤ n) : layerZ n (topI hn) = (n : ℤ) - 1 := by
  simp only [layerZ, topI]; omega

theorem layerZ_botI (hn : 2 ≤ n) : layerZ n (botI hn) = -((n : ℤ) - 1) := by
  simp only [layerZ, botI]; omega

/-- A face letter as a move. -/
def faceMove (hn : 2 ≤ n) (l : TLet) : Move n :=
  (l.1, if l.2.1 then topI hn else botI hn, dirTurn l.2.2)

/-- A row letter as a move, on the row `i`. -/
def rowMove (i : Fin n) (l : TLet) : Move n :=
  (l.1, if l.2.1 then Fin.rev i else i, dirTurn l.2.2)

/-- A word of face letters. -/
def faceW (hn : 2 ≤ n) (f : List TLet) : Word n := f.map (faceMove hn)

/-- A piece, played on the row `i`. -/
def pieceW (hn : 2 ≤ n) (i : Fin n) (p : TPiece) : Word n :=
  faceW hn p.f ++ [rowMove i p.r] ++ Word.inv (faceW hn p.f)

/-- A template, played on the row `i`. -/
def tmplW (hn : 2 ≤ n) (i : Fin n) (τ : Tmpl) : Word n := τ.flatMap (pieceW hn i)

theorem faceW_isQ (hn : 2 ≤ n) (f : List TLet) : ∀ m ∈ faceW hn f, IsQ m := by
  intro m hm
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hm
  exact isQ_dirTurn _ _ _

theorem pieceW_isQ (hn : 2 ≤ n) (i : Fin n) (p : TPiece) : ∀ m ∈ pieceW hn i p, IsQ m := by
  intro m hm
  simp only [pieceW, List.mem_append, List.mem_singleton] at hm
  rcases hm with (h | h) | h
  · exact faceW_isQ hn _ m h
  · subst h; exact isQ_dirTurn _ _ _
  · exact Word.inv_isQ _ (faceW_isQ hn _) m h

theorem tmplW_isQ (hn : 2 ≤ n) (i : Fin n) (τ : Tmpl) : ∀ m ∈ tmplW hn i τ, IsQ m := by
  intro m hm
  obtain ⟨p, _, h⟩ := List.mem_flatMap.1 hm
  exact pieceW_isQ hn i p m h

theorem tmplW_length (hn : 2 ≤ n) (i : Fin n) (τ : Tmpl) :
    (tmplW hn i τ).length = tmplLen τ := by
  induction τ with
  | nil => rfl
  | cons p t ih =>
    simp only [tmplLen, tmplW, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons] at *
    rw [ih]
    simp only [pieceW, faceW, List.length_append, Word.inv_length, List.length_map,
      List.length_singleton]
    ring

theorem Rv_pieceW (v : Sticker n) (hn : 2 ≤ n) (i : Fin n) (p : TPiece) :
    Rv v (pieceW hn i p) =
      Rv v (faceW hn p.f) * rvL v (rowMove i p.r) * (Rv v (faceW hn p.f))⁻¹ := by
  simp only [pieceW, Rv_append, Rv_inv v _ (faceW_isQ hn _), Rv_cons, Rv_nil, mul_one]

theorem Rv_tmplW (v : Sticker n) (hn : 2 ≤ n) (i : Fin n) (τ : Tmpl) :
    Rv v (tmplW hn i τ) = (τ.map fun p => Rv v (pieceW hn i p)).prod :=
  Rv_flatMap v τ _

/-! ### Rows not touching an orbit -/

theorem rvL_rowMove_clear (i j i' : Fin n) (h : Clear n (layerZ n i) (layerZ n j) (layerZ n i'))
    (r : TLet) : rvL (rep i j) (rowMove i' r) = 1 := by
  obtain ⟨a, s, d⟩ := r
  simp only [rowMove]
  rw [rvL_dir]
  have : rvG (rep i j) a (if s then Fin.rev i' else i') = 1 := by
    apply rvG_clear
    split_ifs
    · rw [layerZ_rev]; exact h.neg
    · exact h
  rw [this]
  cases d <;> simp

theorem Rv_pieceW_clear (hn : 2 ≤ n) (i j i' : Fin n)
    (h : Clear n (layerZ n i) (layerZ n j) (layerZ n i')) (p : TPiece) :
    Rv (rep i j) (pieceW hn i' p) = 1 := by
  rw [Rv_pieceW, rvL_rowMove_clear i j i' h]
  simp

theorem Rv_tmplW_clear (hn : 2 ≤ n) (i j i' : Fin n)
    (h : Clear n (layerZ n i) (layerZ n j) (layerZ n i')) (τ : Tmpl) :
    Rv (rep i j) (tmplW hn i' τ) = 1 := by
  rw [Rv_tmplW]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  exact Rv_pieceW_clear hn i j i' h p

/-! ### The constants on generic orbits -/

theorem rvL_faceMove_generic (hn : 2 ≤ n) {i j : Fin n} (hG : Generic i j) (l : TLet) :
    rvL (rep i j) (faceMove hn l) = faceA l := by
  obtain ⟨a, s, d⟩ := l
  simp only [faceMove, faceA]
  rw [rvL_dir]
  congr 1
  cases s
  · simp only [Bool.false_eq_true, if_false]
    exact rvG_generic hG a _ (by simp [ValidC]) (by rw [layerZ_botI]; simp [gval])
  · simp only [if_true]
    exact rvG_generic hG a _ (by simp [ValidC]) (by rw [layerZ_topI]; simp [gval])

theorem Rv_faceW_generic (hn : 2 ≤ n) {i j : Fin n} (hG : Generic i j) (f : List TLet) :
    Rv (rep i j) (faceW hn f) = faceVal f := by
  induction f with
  | nil => rfl
  | cons l t ih =>
    simp only [faceW, faceVal, List.map_cons, Rv_cons, List.prod_cons] at *
    rw [ih, rvL_faceMove_generic hn hG]

theorem rvL_rowMove_target {i j : Fin n} (hG : Generic i j) (r : TLet) :
    rvL (rep i j) (rowMove i r) = rowT r := by
  obtain ⟨a, s, d⟩ := r
  simp only [rowMove, rowT]
  rw [rvL_dir]
  congr 1
  cases s
  · simp only [Bool.false_eq_true, if_false]
    exact rvG_generic hG a _ (by simp [ValidC]) (by simp [gval])
  · simp only [if_true]
    exact rvG_generic hG a _ (by simp [ValidC]) (by rw [layerZ_rev]; simp [gval])

theorem rvL_rowMove_mirror {i j i' : Fin n} (hG : Generic i j) (hi' : layerZ n i' = -layerZ n j)
    (r : TLet) : rvL (rep i j) (rowMove i' r) = rowM r := by
  obtain ⟨a, s, d⟩ := r
  simp only [rowMove, rowM]
  rw [rvL_dir]
  congr 1
  cases s
  · simp only [Bool.false_eq_true, if_false]
    exact rvG_generic hG a _ (by simp [ValidC]) (by rw [hi']; simp [gval])
  · simp only [if_true]
    exact rvG_generic hG a _ (by simp [ValidC]) (by rw [layerZ_rev, hi']; simp [gval])

/-- The template on its target orbit. -/
theorem Rv_tmplW_target (hn : 2 ≤ n) {i j : Fin n} (hG : Generic i j) (τ : Tmpl) :
    Rv (rep i j) (tmplW hn i τ) = evalT τ := by
  rw [Rv_tmplW, evalT]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [Rv_pieceW, Rv_faceW_generic hn hG, rvL_rowMove_target hG]
  rfl

/-- The template on its mirror orbit. -/
theorem Rv_tmplW_mirror (hn : 2 ≤ n) {i j i' : Fin n} (hG : Generic i j)
    (hi' : layerZ n i' = -layerZ n j) (τ : Tmpl) :
    Rv (rep i j) (tmplW hn i' τ) = evalTm τ := by
  rw [Rv_tmplW, evalTm]
  congr 1
  apply List.map_congr_left
  intro p _
  rw [Rv_pieceW, Rv_faceW_generic hn hG, rvL_rowMove_mirror hG hi']
  rfl

/-- The column turned on its target orbit. -/
theorem rvL_col_target {i j : Fin n} (hG : Generic i j) (d : Bool) :
    rvL (rep i j) (.x, j, dirTurn d) = dpow d colK := by
  rw [rvL_dir]
  congr 1
  exact rvG_generic hG .x _ (by simp [ValidC]) (by simp [gval])

/-- The column turned on its mirror orbit. -/
theorem rvL_col_mirror {i j j' : Fin n} (hG : Generic i j) (hj' : layerZ n j' = -layerZ n i)
    (d : Bool) : rvL (rep i j) (.x, j', dirTurn d) = dpow d colM := by
  rw [rvL_dir]
  congr 1
  exact rvG_generic hG .x _ (by simp [ValidC]) (by rw [hj']; simp [gval])

/-- A clear column. -/
theorem rvL_col_clear (i j j' : Fin n) (h : Clear n (layerZ n i) (layerZ n j) (layerZ n j'))
    (d : Bool) : rvL (rep i j) (.x, j', dirTurn d) = 1 := by
  rw [rvL_dir, rvG_clear i j j' h]
  cases d <;> simp

/-! ### Slices of one axis commute -/

theorem rvG_x_apply (v : Sticker n) (l : Fin n) (k : Fin 24) :
    rvG v .x l k = if clamp n (Axis.x.coord (act k v.1)) = layerZ n l then mul (rx .x) k else k := by
  simp only [rvG]
  rw [condPerm_apply]
  rfl

theorem rvG_x_commute (v : Sticker n) (l l' : Fin n) : Commute (rvG v .x l) (rvG v .x l') := by
  have step : ∀ (m : Fin n) (t : Fin 24), clamp n (Axis.x.coord (act t v.1)) = layerZ n m →
      rvG v .x m t = mul (rx .x) t := fun m t h => by rw [rvG_x_apply, if_pos h]
  have stay : ∀ (m : Fin n) (t : Fin 24), ¬ clamp n (Axis.x.coord (act t v.1)) = layerZ n m →
      rvG v .x m t = t := fun m t h => by rw [rvG_x_apply, if_neg h]
  have hc : ∀ t : Fin 24, clamp n (Axis.x.coord (act (mul (rx .x) t) v.1)) =
      clamp n (Axis.x.coord (act t v.1)) := by
    intro t
    rw [act_mul, coord_rx]
  apply Equiv.ext
  intro k
  simp only [Perm.mul_apply]
  by_cases h1 : clamp n (Axis.x.coord (act k v.1)) = layerZ n l <;>
    by_cases h2 : clamp n (Axis.x.coord (act k v.1)) = layerZ n l'
  · rw [step l' k h2, step l _ (by rw [hc]; exact h1), step l k h1,
      step l' _ (by rw [hc]; exact h2)]
  · rw [stay l' k h2, step l k h1, stay l' _ (by rw [hc]; exact h2)]
  · rw [step l' k h2, stay l _ (by rw [hc]; exact h1), stay l k h1, step l' k h2]
  · rw [stay l' k h2, stay l k h1, stay l' k h2]

/-- A column turn. -/
noncomputable def colT (v : Sticker n) (d : Bool) (j : Fin n) : Perm (Fin 24) :=
  rvL v (.x, j, dirTurn d)

theorem colT_not (v : Sticker n) (d : Bool) (j : Fin n) : colT v (!d) j = (colT v d j)⁻¹ := by
  simp only [colT, rvL_dir, dpow_not]

theorem colT_commute (v : Sticker n) (d d' : Bool) (j j' : Fin n) :
    Commute (colT v d j) (colT v d' j') := by
  simp only [colT, rvL_dir]
  have h := rvG_x_commute v j j'
  cases d <;> cases d' <;> simp only [dpow_true, dpow_false]
  · exact h.inv_left.inv_right
  · exact h.inv_left
  · exact h.inv_right
  · exact h

/-- Column turns in one direction, then the other, cancel. -/
theorem colT_cancel (v : Sticker n) (d : Bool) (L : List (Fin n)) :
    (L.map (colT v d)).prod * (L.map (colT v (!d))).prod = 1 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc : Commute (t.map (colT v d)).prod (colT v (!d) a) := by
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      exact colT_commute v _ _ _ _
    calc colT v d a * (t.map (colT v d)).prod * (colT v (!d) a * (t.map (colT v (!d))).prod)
        = colT v d a * ((t.map (colT v d)).prod * colT v (!d) a) * (t.map (colT v (!d))).prod := by
          group
      _ = colT v d a * colT v (!d) a *
            ((t.map (colT v d)).prod * (t.map (colT v (!d))).prod) := by
          rw [hc.eq]; group
      _ = 1 := by rw [ih, colT_not]; simp

/-! ### Two list lemmas -/

theorem prod_map_single {ι G : Type*} [Monoid G] (L : List ι) (hL : L.Nodup) (f : ι → G) (a : ι)
    (ha : a ∈ L) (h : ∀ x ∈ L, x ≠ a → f x = 1) : (L.map f).prod = f a := by
  induction L with
  | nil => simp at ha
  | cons x t ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.1 hL
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 ha with rfl | hat
    · have : (t.map f).prod = 1 := by
        apply List.prod_eq_one
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact h z (List.mem_cons_of_mem _ hz) (fun he => hx (he ▸ hz))
      rw [this, mul_one]
    · have hne : x ≠ a := fun he => hx (he ▸ hat)
      rw [h x List.mem_cons_self hne, one_mul]
      exact ih ht hat (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem perm_flatMap_filter {ι β : Type*} [DecidableEq β] (P : List β) (hP : P.Nodup) (L : List ι)
    (hL : L.Nodup) (f : ι → β) (hf : ∀ x ∈ L, f x ∈ P) :
    (P.flatMap fun p => L.filter fun x => f x = p).Perm L := by
  rw [List.perm_ext_iff_of_nodup]
  · intro x
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, _, h, _⟩
      exact h
    · intro h
      exact ⟨f x, hf x h, h, rfl⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun p _ => hL.filter _, ?_⟩
    refine List.Pairwise.imp ?_ hP
    intro a b hab x hx hx'
    simp only [List.mem_filter, decide_eq_true_eq] at hx hx'
    exact hab (hx.2.symm.trans hx'.2)
  · exact hL

theorem length_flatMap_le {ι κ : Type*} (l : List ι) (f : ι → List κ) (L : ℕ)
    (h : ∀ x ∈ l, (f x).length ≤ L) : (l.flatMap f).length ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    nlinarith

end RubiksGN
