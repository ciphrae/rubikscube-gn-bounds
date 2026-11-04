import RubiksGN.RotData

/-!
# The `n × n × n` Rubik's cube

A sticker is an integer vector on the surface of the cube `[-n,n]³`: one coordinate is `±n` and the
other two lie in `{-(n-1), -(n-3), …, n-1}`. A *move* rotates one of the `n` layers about one of the
three axes; the layer containing a sticker is read off by clamping `±n` to `±(n-1)`.
-/

open Equiv

namespace RubiksGN

theorem perm_inv_apply {α : Type*} (g : Perm α) (x : α) : g⁻¹ (g x) = x := by simp

theorem perm_apply_inv {α : Type*} (g : Perm α) (x : α) : g (g⁻¹ x) = x := by simp

/-- The coordinates of the cubies along one axis. -/
def IsCoord (n : ℕ) (c : ℤ) : Prop :=
  -((n : ℤ) - 1) ≤ c ∧ c ≤ (n : ℤ) - 1 ∧ (c + (n : ℤ) - 1) % 2 = 0

/-- Stickers: exactly one coordinate is `±n`, the two others are cubie coordinates. -/
def IsSticker (n : ℕ) : V → Prop
  | (x, y, z) =>
    ((x = n ∨ x = -(n : ℤ)) ∧ IsCoord n y ∧ IsCoord n z) ∨
    (IsCoord n x ∧ (y = n ∨ y = -(n : ℤ)) ∧ IsCoord n z) ∨
    (IsCoord n x ∧ IsCoord n y ∧ (z = n ∨ z = -(n : ℤ)))

/-- The stickers of the `n × n × n` cube (there are `6 n²`). -/
abbrev Sticker (n : ℕ) := {v : V // IsSticker n v}

/-- The rotation with index `i`. -/
def act (i : Fin 24) (v : V) : V := actN i v

/-- Rotation-group multiplication. -/
def mul (i j : Fin 24) : Fin 24 := Fin.ofNat 24 ((mulTab.getD i []).getD j 0)

/-- Rotation-group inverse. -/
def inv (i : Fin 24) : Fin 24 := Fin.ofNat 24 (invTab.getD i 0)

/-- The three axes. -/
inductive Axis | x | y | z
  deriving DecidableEq, Repr

instance : Fintype Axis := ⟨{.x, .y, .z}, by intro a; cases a <;> simp⟩

/-- The coordinate along an axis. -/
def Axis.coord : Axis → V → ℤ
  | .x, v => v.1
  | .y, v => v.2.1
  | .z, v => v.2.2

/-- The quarter turn about an axis, as a rotation index. -/
def rx : Axis → Fin 24
  | .x => Fin.ofNat 24 rxN
  | .y => Fin.ofNat 24 ryN
  | .z => Fin.ofNat 24 rzN

/-- The layer coordinate of a sticker coordinate: `±n` is clamped to `±(n-1)`. -/
def clamp (n : ℕ) (t : ℤ) : ℤ :=
  if t = n then (n : ℤ) - 1 else if t = -(n : ℤ) then -((n : ℤ) - 1) else t

theorem isCoord_neg (n : ℕ) (c : ℤ) : IsCoord n (-c) ↔ IsCoord n c := by
  simp only [IsCoord]; omega

theorem isFace_neg (n : ℕ) (c : ℤ) : (-c = n ∨ -c = -(n : ℤ)) ↔ (c = n ∨ c = -(n : ℤ)) := by
  omega

set_option maxHeartbeats 8000000 in
theorem act_isSticker (n : ℕ) (i : Fin 24) {v : V} (hv : IsSticker n v) :
    IsSticker n (act i v) := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨k, hk⟩ := i
  simp only [IsSticker] at hv
  interval_cases k <;> simp only [act, actN, IsSticker, isCoord_neg, isFace_neg] <;> tauto

theorem act_zero (v : V) : act 0 v = v := by
  obtain ⟨x, y, z⟩ := v; rfl

/-- The matrix of a rotation, read off from the images of the basis vectors. -/
def mat (i : Fin 24) (r c : Fin 3) : ℤ :=
  let e : V := match c with
    | 0 => (1, 0, 0)
    | 1 => (0, 1, 0)
    | 2 => (0, 0, 1)
  match r with
  | 0 => (act i e).1
  | 1 => (act i e).2.1
  | 2 => (act i e).2.2

set_option maxHeartbeats 8000000 in
theorem act_linear (i : Fin 24) (x y z : ℤ) :
    act i (x, y, z) =
      (mat i 0 0 * x + mat i 0 1 * y + mat i 0 2 * z,
       mat i 1 0 * x + mat i 1 1 * y + mat i 1 2 * z,
       mat i 2 0 * x + mat i 2 1 * y + mat i 2 2 * z) := by
  obtain ⟨k, hk⟩ := i
  interval_cases k <;> simp [act, actN, mat]

theorem mat_mul : ∀ (i j : Fin 24) (r c : Fin 3),
    mat (mul i j) r c = mat i r 0 * mat j 0 c + mat i r 1 * mat j 1 c + mat i r 2 * mat j 2 c := by
  decide +kernel

theorem act_mul (i j : Fin 24) (v : V) : act (mul i j) v = act i (act j v) := by
  obtain ⟨x, y, z⟩ := v
  rw [act_linear, act_linear j, act_linear i]
  simp only [mat_mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem mul_inv_self : ∀ i : Fin 24, mul i (inv i) = 0 := by decide +kernel
theorem inv_mul_self : ∀ i : Fin 24, mul (inv i) i = 0 := by decide +kernel
theorem zero_mul : ∀ i : Fin 24, mul 0 i = i := by decide +kernel
theorem mul_zero : ∀ i : Fin 24, mul i 0 = i := by decide +kernel
theorem mul_assoc : ∀ i j k : Fin 24, mul (mul i j) k = mul i (mul j k) := by decide +kernel

theorem act_inv_act (i : Fin 24) (v : V) : act (inv i) (act i v) = v := by
  rw [← act_mul, inv_mul_self, act_zero]

theorem act_act_inv (i : Fin 24) (v : V) : act i (act (inv i) v) = v := by
  rw [← act_mul, mul_inv_self, act_zero]

/-- A rotation as a permutation of the stickers. -/
def actPerm (n : ℕ) (i : Fin 24) : Perm (Sticker n) where
  toFun q := ⟨act i q.1, act_isSticker n i q.2⟩
  invFun q := ⟨act (inv i) q.1, act_isSticker n _ q.2⟩
  left_inv q := Subtype.ext (act_inv_act i q.1)
  right_inv q := Subtype.ext (act_act_inv i q.1)

@[simp] theorem actPerm_val (n : ℕ) (i : Fin 24) (q : Sticker n) :
    (actPerm n i q).1 = act i q.1 := rfl

@[simp] theorem actPerm_inv_val (n : ℕ) (i : Fin 24) (q : Sticker n) :
    ((actPerm n i)⁻¹ q).1 = act (inv i) q.1 := rfl

theorem actPerm_mul (n : ℕ) (i j : Fin 24) : actPerm n (mul i j) = actPerm n i * actPerm n j := by
  ext q : 2
  simp [Perm.mul_apply, act_mul]

theorem actPerm_inv (n : ℕ) (i : Fin 24) : (actPerm n i)⁻¹ = actPerm n (inv i) := by
  ext q : 2
  rfl

/-- Rotate exactly those points satisfying an invariant predicate. -/
def condPerm {α : Type*} (ρ : Perm α) (P : α → Prop) [DecidablePred P]
    (h : ∀ a, P (ρ a) ↔ P a) : Perm α where
  toFun a := if P a then ρ a else a
  invFun a := if P a then ρ.symm a else a
  left_inv a := by
    by_cases ha : P a
    · have hb : P (ρ a) := (h a).2 ha
      simp only [if_pos ha, if_pos hb, Equiv.symm_apply_apply]
    · simp only [if_neg ha]
  right_inv a := by
    by_cases ha : P a
    · have hb : P (ρ.symm a) := by
        have := h (ρ.symm a)
        rw [Equiv.apply_symm_apply] at this
        exact this.1 ha
      simp only [if_pos ha, if_pos hb, Equiv.apply_symm_apply]
    · simp only [if_neg ha]

theorem condPerm_apply {α : Type*} (ρ : Perm α) (P : α → Prop) [DecidablePred P]
    (h : ∀ a, P (ρ a) ↔ P a) (a : α) : condPerm ρ P h a = if P a then ρ a else a := rfl

theorem condPerm_inv_apply {α : Type*} (ρ : Perm α) (P : α → Prop) [DecidablePred P]
    (h : ∀ a, P (ρ a) ↔ P a) (a : α) : (condPerm ρ P h)⁻¹ a = if P a then ρ⁻¹ a else a := rfl

theorem coord_rx : ∀ (a : Axis) (v : V), a.coord (act (rx a) v) = a.coord v := by
  rintro a ⟨x, y, z⟩
  cases a <;> rfl

open Classical in
/-- Rotate all layers of an axis whose coordinate satisfies `S`. -/
noncomputable def slice (n : ℕ) (a : Axis) (S : ℤ → Prop) : Perm (Sticker n) :=
  condPerm (actPerm n (rx a)) (fun q => S (clamp n (a.coord q.1))) (fun q => by
    simp [coord_rx])

theorem slice_apply_of (n : ℕ) (a : Axis) (S : ℤ → Prop) (q : Sticker n)
    (h : S (clamp n (a.coord q.1))) : slice n a S q = actPerm n (rx a) q := by
  classical
  simp [slice, condPerm_apply, h]

theorem slice_apply_not (n : ℕ) (a : Axis) (S : ℤ → Prop) (q : Sticker n)
    (h : ¬ S (clamp n (a.coord q.1))) : slice n a S q = q := by
  classical
  simp [slice, condPerm_apply, h]

theorem slice_inv_apply_of (n : ℕ) (a : Axis) (S : ℤ → Prop) (q : Sticker n)
    (h : S (clamp n (a.coord q.1))) : (slice n a S)⁻¹ q = (actPerm n (rx a))⁻¹ q := by
  classical
  simp [slice, condPerm_inv_apply, h]

theorem slice_inv_apply_not (n : ℕ) (a : Axis) (S : ℤ → Prop) (q : Sticker n)
    (h : ¬ S (clamp n (a.coord q.1))) : (slice n a S)⁻¹ q = q := by
  classical
  simp [slice, condPerm_inv_apply, h]

/-- The integer coordinate of the layer with index `i`. -/
def layerZ (n : ℕ) (i : Fin n) : ℤ := 2 * (i.val : ℤ) - ((n : ℤ) - 1)

/-- A quarter turn of one layer. -/
noncomputable def quarter (n : ℕ) (a : Axis) (i : Fin n) : Perm (Sticker n) :=
  slice n a (· = layerZ n i)

/-- The three amounts by which a layer can be turned. -/
inductive Turn | cw | half | ccw
  deriving DecidableEq, Repr

instance : Fintype Turn := ⟨{.cw, .half, .ccw}, by intro a; cases a <;> simp⟩

/-- A move: an axis, a layer and an amount of turning. There are `9 n` moves. -/
abbrev Move (n : ℕ) := Axis × Fin n × Turn

/-- The permutation of the stickers performed by a move. -/
noncomputable def Move.toPerm {n : ℕ} : Move n → Perm (Sticker n)
  | (a, i, .cw) => quarter n a i
  | (a, i, .half) => quarter n a i * quarter n a i
  | (a, i, .ccw) => (quarter n a i)⁻¹

/-- Words of moves; the head of the list is applied last. -/
abbrev Word (n : ℕ) := List (Move n)

/-- The permutation performed by a word. -/
noncomputable def Word.eval {n : ℕ} (w : Word n) : Perm (Sticker n) := (w.map Move.toPerm).prod

/-- The cube group: everything reachable from the solved cube. -/
noncomputable def cubeGroup (n : ℕ) : Subgroup (Perm (Sticker n)) :=
  Subgroup.closure (Set.range Move.toPerm)

/-- The two standard metrics: half turns cost one move (`htm`), or are not allowed (`qtm`). -/
inductive Metric | htm | qtm
  deriving DecidableEq, Repr

/-- The moves allowed in a metric. -/
def Metric.allows {n : ℕ} : Metric → Move n → Prop
  | .htm, _ => True
  | .qtm, m => m.2.2 ≠ .half

/-- `k` moves suffice to return every labelled position to the identity. -/
def LabelledSolvable (μ : Metric) (n k : ℕ) : Prop :=
  ∀ g ∈ cubeGroup n, ∃ w : Word n, (∀ m ∈ w, μ.allows m) ∧ w.length ≤ k ∧ w.eval * g = 1

/-- God's number for the labelled cube: every sticker is distinguishable, and the goal is exactly
the identity. -/
noncomputable def godLabelled (μ : Metric) (n : ℕ) : ℕ := sInf {k | LabelledSolvable μ n k}

/-- The face a sticker lies on. -/
def faceOf {n : ℕ} (q : Sticker n) : Fin 6 :=
  if q.1.2.2 = n then 0 else if q.1.2.2 = -(n : ℤ) then 1
  else if q.1.2.1 = n then 2 else if q.1.2.1 = -(n : ℤ) then 3
  else if q.1.1 = n then 4 else 5

/-- A colouring is solved when every face is monochromatic. -/
def IsSolved {n : ℕ} (c : Sticker n → Fin 6) : Prop :=
  ∀ q q', faceOf q = faceOf q' → c q = c q'

/-- The colouring seen after applying `g` to the solved cube. -/
def colouring {n : ℕ} (g : Perm (Sticker n)) : Sticker n → Fin 6 := fun q => faceOf (g⁻¹ q)

/-- `k` moves suffice to make every face of every reachable coloured position monochromatic. -/
def ColouredSolvable (μ : Metric) (n k : ℕ) : Prop :=
  ∀ g ∈ cubeGroup n, ∃ w : Word n, (∀ m ∈ w, μ.allows m) ∧ w.length ≤ k ∧
    IsSolved (colouring (w.eval * g))

/-- God's number for the real, coloured cube: stickers of one colour are indistinguishable, and any
position with monochromatic faces counts as solved. -/
noncomputable def godColoured (μ : Metric) (n : ℕ) : ℕ := sInf {k | ColouredSolvable μ n k}

end RubiksGN
