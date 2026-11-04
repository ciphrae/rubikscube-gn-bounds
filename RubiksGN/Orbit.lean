import RubiksGN.GadgetAction

/-!
# Orbit coordinates and the gadget words

`gadgetW L X Y` is a word of `2|X| + 2|Y| + 4` quarter turns acting on every orbit `(i, j) ∈ X × Y` by
the same 3-cycle `lp L` of the 24 orbit coordinates, and fixing all other orbits considered here.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

theorem layerZ_isCoord (i : Fin n) : IsCoord n (layerZ n i) := by
  have := i.isLt
  simp only [IsCoord, layerZ]
  omega

/-- The sticker `(layerZ i, layerZ j, n)` on the top face. -/
def rep (i j : Fin n) : Sticker n :=
  ⟨(layerZ n i, layerZ n j, (n : ℤ)),
    Or.inr (Or.inr ⟨layerZ_isCoord i, layerZ_isCoord j, Or.inl rfl⟩)⟩

/-- Orbit coordinates: the image of `v` under the rotation `k`. -/
def e (v : Sticker n) (k : Fin 24) : Sticker n := actPerm n k v

theorem actPerm_e (τ k : Fin 24) (v : Sticker n) : actPerm n τ (e v k) = e v (mul τ k) := by
  apply Subtype.ext
  simp [e, act_mul]

theorem e_zero (v : Sticker n) : e v 0 = v := by
  apply Subtype.ext
  simp [e, act_zero]

theorem exists_layer {c : ℤ} (h : IsCoord n c) : ∃ i : Fin n, layerZ n i = c := by
  simp only [IsCoord] at h
  refine ⟨⟨((c + n - 1) / 2).toNat, by omega⟩, ?_⟩
  simp only [layerZ]
  omega

set_option maxHeartbeats 8000000 in
theorem top_unique (t : Fin 24) (x y x' y' N : ℤ) (hN : 0 < N)
    (h : act t (x, y, N) = (x', y', N)) (h1 : x < 0) (h2 : 0 ≤ y) (h3 : x' < 0) (h4 : 0 ≤ y')
    (h5 : -N < x) (h6 : y < N) :
    t.val = 0 ∧ x = x' ∧ y = y' := by
  obtain ⟨k, hk⟩ := t
  interval_cases k <;> simp only [act, actN, Prod.mk.injEq] at h <;>
    first
    | exact ⟨rfl, by omega, by omega⟩
    | omega

set_option maxHeartbeats 8000000 in
theorem center_unique (t : Fin 24) (x' y' N : ℤ) (hN : 0 < N)
    (h : act t (0, 0, N) = (x', y', N)) (h3 : x' < 0) : False := by
  obtain ⟨k, hk⟩ := t
  interval_cases k <;> simp only [act, actN, Prod.mk.injEq] at h <;> omega

theorem inv_mul_eq_zero : ∀ a b : Fin 24, mul (inv a) b = 0 → b = a := by decide +kernel

/-- The domain of orbit representatives. -/
def InDom (i j : Fin n) : Prop := layerZ n i < 0 ∧ 0 ≤ layerZ n j

theorem coord_lt_of (i : Fin n) : layerZ n i < n ∧ -(n : ℤ) < layerZ n i := by
  have := layerZ_isCoord i
  simp only [IsCoord] at this
  omega

theorem rep_e_inj (i j i' j' : Fin n) (k k' : Fin 24) (hd : InDom i j) (hd' : InDom i' j')
    (h : e (rep i j) k = e (rep i' j') k') : i = i' ∧ j = j' ∧ k = k' := by
  have hv := congrArg (fun q => (actPerm n (inv k') q).1) h
  simp only [e, actPerm_val, ← act_mul] at hv
  rw [inv_mul_self, act_zero] at hv
  have hn : 0 < (n : ℤ) := by have := i.pos; omega
  obtain ⟨h0, h1, h2⟩ := top_unique _ _ _ _ _ _ hn hv hd.1 hd.2 hd'.1 hd'.2
    (coord_lt_of i).2 (coord_lt_of j).1
  refine ⟨layerZ_inj _ _ h1, layerZ_inj _ _ h2, inv_mul_eq_zero k' k (Fin.ext h0)⟩

/-- The rotation carrying a partner-orbit representative to the second point of the overlap. -/
def kappa : Fin 24 := 8

theorem act_kappa (a b c : ℤ) : act kappa (a, b, c) = (-b, c, -a) := rfl

/-- A row: an inner layer with negative coordinate. -/
def IsRow (i : Fin n) : Prop := 0 < i.val ∧ 2 * i.val + 1 < n

/-- A column: a layer with nonnegative coordinate (the outer layer is allowed). -/
def IsCol (j : Fin n) : Prop := n ≤ 2 * j.val + 1

variable {SX SY : ℤ → Prop}

theorem inZ_index (d : RectData n SX SY) (z : Sticker n) (hz : InZ SX SY z) :
    (∃ i j : Fin n, SX (layerZ n i) ∧ SY (layerZ n j) ∧ z = rep i j) ∨
    (∃ (h0 : 0 < n) (j : Fin n), SY ((n : ℤ) - 1) ∧ SX (-layerZ n j) ∧ 0 ≤ layerZ n j ∧
      z = e (rep ⟨0, h0⟩ j) kappa) := by
  rcases inZ_forms d z hz with ⟨x, y, hx, hy, hcx, hcy, hv⟩ | ⟨x, hx, hy, hcx, hv⟩
  · left
    obtain ⟨i, rfl⟩ := exists_layer hcx
    obtain ⟨j, rfl⟩ := exists_layer hcy
    exact ⟨i, j, hx, hy, Subtype.ext hv⟩
  · right
    have hn0 : 0 < n := by have := d.hn; omega
    have hc : IsCoord n (-x) := (isCoord_neg n x).2 hcx
    obtain ⟨j, hj⟩ := exists_layer hc
    have hxb := d.hX x hx
    refine ⟨hn0, j, hy, by rw [hj, neg_neg]; exact hx, by rw [hj]; omega, ?_⟩
    apply Subtype.ext
    rw [hv]
    show _ = act kappa (layerZ n ⟨0, hn0⟩, layerZ n j, (n : ℤ))
    rw [act_kappa, hj]
    simp [layerZ]

/-- The action of the base commutator on orbit coordinates. -/
def cycFn (da db : Bool) (k : Fin 24) : Fin 24 :=
  if k = 0 then alphaOf da else if k = alphaOf da then betaOf db
  else if k = betaOf db then 0 else k

theorem alpha_ne_zero : ∀ da : Bool, alphaOf da ≠ 0 := by decide +kernel
theorem beta_ne_zero : ∀ db : Bool, betaOf db ≠ 0 := by decide +kernel
theorem beta_ne_alpha : ∀ da db : Bool, betaOf db ≠ alphaOf da := by decide +kernel

theorem clamp_coord {c : ℤ} (h : IsCoord n c) : clamp n c = c := by
  simp only [IsCoord] at h
  exact clamp_of_ne c (by omega) (by omega)

theorem rep_inZ (hn : 2 ≤ n) (i j : Fin n) (hx : SX (layerZ n i)) (hy : SY (layerZ n j)) :
    InZ SX SY (rep i j) := by
  refine ⟨?_, ?_⟩
  · simp only [rep]; rw [clamp_coord (layerZ_isCoord i)]; exact hx
  · have h' : IsSticker n (layerZ n i, layerZ n j, (n : ℤ)) := (rep i j).2
    have hc : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
    refine (Pb_iff SY _ _ _ h').2 ?_
    rw [hc, if_pos rfl, clamp_coord (layerZ_isCoord j)]
    exact hy

/-- All of `Z ∪ aZ ∪ bZ` avoids a sticker, given its orbit coordinates differ. -/
theorem baseC_fix_of_e (d : RectData n SX SY) (da db : Bool) (q : Sticker n)
    (h1 : ∀ i j : Fin n, SX (layerZ n i) → SY (layerZ n j) →
      q ≠ e (rep i j) 0 ∧ q ≠ e (rep i j) (alphaOf da) ∧ q ≠ e (rep i j) (betaOf db))
    (h2 : ∀ (h0 : 0 < n) (j : Fin n), SY ((n : ℤ) - 1) → SX (-layerZ n j) → 0 ≤ layerZ n j →
      q ≠ e (rep ⟨0, h0⟩ j) kappa ∧ q ≠ e (rep ⟨0, h0⟩ j) (mul (alphaOf da) kappa) ∧
      q ≠ e (rep ⟨0, h0⟩ j) (mul (betaOf db) kappa)) :
    baseC da db SX SY q = q := by
  apply baseC_fix d
  intro z hz
  rcases inZ_index d z hz with ⟨i, j, hx, hy, rfl⟩ | ⟨h0, j, hy, hx, hj, rfl⟩
  · obtain ⟨a, b, c⟩ := h1 i j hx hy
    rw [e_zero] at a
    exact ⟨a, b, c⟩
  · obtain ⟨a, b, c⟩ := h2 h0 j hy hx hj
    refine ⟨a, ?_, ?_⟩
    · rw [actPerm_e]; exact b
    · rw [actPerm_e]; exact c

theorem row_domain (d : RectData n SX SY) (i : Fin n) (h : SX (layerZ n i)) :
    layerZ n i < 0 ∧ -((n : ℤ) - 1) < layerZ n i := by
  have := d.hX _ h
  omega

theorem baseC_on (d : RectData n SX SY) (da db : Bool) (i j : Fin n)
    (hx : SX (layerZ n i)) (hy : SY (layerZ n j)) (k : Fin 24) :
    baseC da db SX SY (e (rep i j) k) = e (rep i j) (cycFn da db k) := by
  have hn := d.hn
  have hz := rep_inZ hn i j hx hy
  obtain ⟨h1, h2, h3⟩ := baseC_three d da db _ hz
  have hdom : InDom i j := ⟨(d.hX _ hx).2, d.hY _ hy⟩
  by_cases k0 : k = 0
  · subst k0
    simp only [cycFn, if_true, e_zero]
    exact h1
  by_cases k1 : k = alphaOf da
  · subst k1
    simp only [cycFn, alpha_ne_zero, if_false, if_true]
    exact h2
  by_cases k2 : k = betaOf db
  · subst k2
    simp only [cycFn, beta_ne_zero, beta_ne_alpha, if_false, if_true, e_zero]
    exact h3
  simp only [cycFn, k0, k1, k2, if_false]
  apply baseC_fix_of_e d
  · intro i' j' hx' hy'
    have hd' : InDom i' j' := ⟨(d.hX _ hx').2, d.hY _ hy'⟩
    refine ⟨fun he => k0 (rep_e_inj _ _ _ _ _ _ hdom hd' he).2.2,
      fun he => k1 (rep_e_inj _ _ _ _ _ _ hdom hd' he).2.2,
      fun he => k2 (rep_e_inj _ _ _ _ _ _ hdom hd' he).2.2⟩
  · intro h0 j' _ hx' hj'
    have hd' : InDom (⟨0, h0⟩ : Fin n) j' := by
      refine ⟨?_, hj'⟩
      simp only [layerZ]; omega
    have hne : i ≠ ⟨0, h0⟩ := by
      rintro rfl
      have := (d.hX _ hx).1
      simp only [layerZ] at this
      omega
    refine ⟨fun he => hne (rep_e_inj _ _ _ _ _ _ hdom hd' he).1,
      fun he => hne (rep_e_inj _ _ _ _ _ _ hdom hd' he).1,
      fun he => hne (rep_e_inj _ _ _ _ _ _ hdom hd' he).1⟩

theorem baseC_off (d : RectData n SX SY) (da db : Bool) (i j : Fin n) (hdom : InDom i j)
    (H1 : ¬ (SX (layerZ n i) ∧ SY (layerZ n j)))
    (H2 : ¬ (i.val = 0 ∧ SY ((n : ℤ) - 1) ∧ SX (-layerZ n j))) (k : Fin 24) :
    baseC da db SX SY (e (rep i j) k) = e (rep i j) k := by
  have hn := d.hn
  apply baseC_fix_of_e d
  · intro i' j' hx' hy'
    have hd' : InDom i' j' := ⟨(d.hX _ hx').2, d.hY _ hy'⟩
    have hne : ∀ t, e (rep i j) k ≠ e (rep i' j') t := by
      intro t he
      obtain ⟨rfl, rfl, _⟩ := rep_e_inj _ _ _ _ _ _ hdom hd' he
      exact H1 ⟨hx', hy'⟩
    exact ⟨hne _, hne _, hne _⟩
  · intro h0 j' hyo hx' hj'
    have hd' : InDom (⟨0, h0⟩ : Fin n) j' := by
      refine ⟨?_, hj'⟩
      simp only [layerZ]; omega
    have hne : ∀ t, e (rep i j) k ≠ e (rep ⟨0, h0⟩ j') t := by
      intro t he
      obtain ⟨rfl, rfl, _⟩ := rep_e_inj _ _ _ _ _ _ hdom hd' he
      exact H2 ⟨rfl, hyo, hx'⟩
    exact ⟨hne _, hne _, hne _⟩

theorem baseC_center (d : RectData n SX SY) (da db : Bool) (m : Fin n) (hm : layerZ n m = 0)
    (k : Fin 24) : baseC da db SX SY (e (rep m m) k) = e (rep m m) k := by
  have hN : 0 < (n : ℤ) := by have := m.pos; omega
  have hn := d.hn
  have key : ∀ (i j : Fin n) (t : Fin 24), InDom i j → e (rep m m) k ≠ e (rep i j) t := by
    intro i j t hd he
    have hv := congrArg (fun q => (actPerm n (inv t) q).1) he
    simp only [e, actPerm_val, ← act_mul] at hv
    rw [inv_mul_self, act_zero] at hv
    simp only [rep, hm] at hv
    exact center_unique _ _ _ _ hN hv hd.1
  apply baseC_fix_of_e d
  · intro i' j' hx' hy'
    have hd' : InDom i' j' := ⟨(d.hX _ hx').2, d.hY _ hy'⟩
    exact ⟨key _ _ _ hd', key _ _ _ hd', key _ _ _ hd'⟩
  · intro h0 j' _ _ hj'
    have hd' : InDom (⟨0, h0⟩ : Fin n) j' := by
      refine ⟨?_, hj'⟩
      simp only [layerZ]; omega
    exact ⟨key _ _ _ hd', key _ _ _ hd', key _ _ _ hd'⟩

/-! ### Letters: the 3-cycles of orbit coordinates -/

/-- A 3-cycle `a → b → c → a`. -/
def cyc3 (a b c : Fin 24) : Perm (Fin 24) := swap a b * swap b c

/-- A letter: a rotation, the directions of the two slice sets, and whether to invert. -/
abbrev Letter := Fin 24 × Bool × Bool × Bool

/-- The permutation of orbit coordinates performed by a letter. -/
def lp (L : Letter) : Perm (Fin 24) :=
  let c := cyc3 L.1 (mul L.1 (alphaOf L.2.1)) (mul L.1 (betaOf L.2.2.1))
  if L.2.2.2 then c⁻¹ else c

theorem cycFn_spec : ∀ (τ : Fin 24) (da db : Bool) (k : Fin 24),
    mul τ (cycFn da db (mul (inv τ) k)) =
      cyc3 τ (mul τ (alphaOf da)) (mul τ (betaOf db)) k := by
  intro τ da db k
  cases da <;> cases db <;> revert τ k <;> decide +kernel

/-- The turn in a direction. -/
def dirTurn (d : Bool) : Turn := if d then .cw else .ccw

/-- The top layer index. -/
def topI (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- The set of layer coordinates of a finite set of layers. -/
def SOf (X : Finset (Fin n)) (l : ℤ) : Prop := ∃ i ∈ X.toList, l = layerZ n i

theorem sOf_layer (X : Finset (Fin n)) (i : Fin n) : SOf X (layerZ n i) ↔ i ∈ X := by
  simp only [SOf, Finset.mem_toList]
  constructor
  · rintro ⟨j, hj, h⟩
    rwa [layerZ_inj _ _ h]
  · intro h
    exact ⟨i, h, rfl⟩

/-- The base word of the commutator. -/
noncomputable def baseW (hn : 2 ≤ n) (da db : Bool) (X Y : Finset (Fin n)) : Word n :=
  sliceW .x X.toList (dirTurn da) ++ (Axis.z, topI hn, Turn.cw) ::
  sliceW .x Y.toList (dirTurn db) ++ (Axis.z, topI hn, Turn.ccw) ::
  sliceW .x X.toList (dirTurn (!da)) ++ (Axis.z, topI hn, Turn.cw) ::
  sliceW .x Y.toList (dirTurn (!db)) ++ [(Axis.z, topI hn, Turn.ccw)]

theorem sliceW_dir (L : Finset (Fin n)) (d : Bool) :
    Word.eval (sliceW .x L.toList (dirTurn d)) = sl d (SOf L) := by
  cases d
  · simp only [dirTurn, Bool.false_eq_true, if_false, sl]
    rw [sliceW_eval_ccw _ _ (Finset.nodup_toList L)]; rfl
  · simp only [dirTurn, if_true, sl]
    rw [sliceW_eval_cw _ _ (Finset.nodup_toList L)]; rfl

theorem top_toPerm (hn : 2 ≤ n) : Move.toPerm ((Axis.z, topI hn, Turn.cw) : Move n) = Uop n := by
  have : layerZ n (topI hn) = (n : ℤ) - 1 := by
    simp only [layerZ, topI]; omega
  simp only [Move.toPerm, quarter, Uop, this]

theorem top_toPerm' (hn : 2 ≤ n) : Move.toPerm ((Axis.z, topI hn, Turn.ccw) : Move n) = (Uop n)⁻¹ := by
  have : layerZ n (topI hn) = (n : ℤ) - 1 := by
    simp only [layerZ, topI]; omega
  simp only [Move.toPerm, quarter, Uop, this]

theorem baseW_eval (hn : 2 ≤ n) (da db : Bool) (X Y : Finset (Fin n)) :
    Word.eval (baseW hn da db X Y) = baseC da db (SOf X) (SOf Y) := by
  simp only [baseW, baseC, bOp, Word.eval_append, Word.eval_cons, Word.eval_nil, mul_one,
    sliceW_dir, top_toPerm, top_toPerm', mul_inv_rev, inv_inv, sl_inv, _root_.mul_assoc]

theorem isQ_dirTurn (a : Axis) (i : Fin n) (d : Bool) : IsQ ((a, i, dirTurn d) : Move n) := by
  cases d <;> simp [IsQ, dirTurn]

theorem baseW_isQ (hn : 2 ≤ n) (da db : Bool) (X Y : Finset (Fin n)) :
    ∀ m ∈ baseW hn da db X Y, IsQ m := by
  intro m hm
  have hs : ∀ (L : List (Fin n)) (d : Bool), ∀ m ∈ sliceW .x L (dirTurn d), IsQ m := by
    intro L d m hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hm
    exact isQ_dirTurn _ _ _
  simp only [baseW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with (((h | h | h) | h | h) | h | h) | h <;>
    first
    | exact hs _ _ _ h
    | (subst h; simp [IsQ])

theorem baseW_length (hn : 2 ≤ n) (da db : Bool) (X Y : Finset (Fin n)) :
    (baseW hn da db X Y).length = 2 * X.card + 2 * Y.card + 4 := by
  simp only [baseW, sliceW, List.length_append, List.length_cons, List.length_map,
    Finset.length_toList, List.length_nil]
  ring

/-- The word of a letter on a rectangle. -/
noncomputable def gadgetW (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) : Word n :=
  let w := (baseW hn L.2.1 L.2.2.1 X Y).map (Move.relabel L.1)
  if L.2.2.2 then Word.inv w else w

theorem gadgetW_length (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) :
    (gadgetW hn L X Y).length = 2 * X.card + 2 * Y.card + 4 := by
  simp only [gadgetW]
  split_ifs
  · rw [Word.inv_length, List.length_map, baseW_length]
  · rw [List.length_map, baseW_length]

theorem relabel_isQ (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) :
    ∀ m ∈ (baseW hn L.2.1 L.2.2.1 X Y).map (Move.relabel L.1), IsQ m := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  exact isQ_relabel _ _ (baseW_isQ _ _ _ _ _ _ hx)

theorem gadgetW_isQ (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) :
    ∀ m ∈ gadgetW hn L X Y, IsQ m := by
  simp only [gadgetW]
  split_ifs
  · exact Word.inv_isQ _ (relabel_isQ hn L X Y)
  · exact relabel_isQ hn L X Y

/-- The permutation performed by the relabelled commutator, before inversion. -/
noncomputable def gammaP (L : Letter) (X Y : Finset (Fin n)) : Perm (Sticker n) :=
  actPerm n L.1 * baseC L.2.1 L.2.2.1 (SOf X) (SOf Y) * (actPerm n L.1)⁻¹

theorem gadgetW_eval (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) :
    Word.eval (gadgetW hn L X Y) =
      if L.2.2.2 then (gammaP L X Y)⁻¹ else gammaP L X Y := by
  have h : Word.eval ((baseW hn L.2.1 L.2.2.1 X Y).map (Move.relabel L.1)) = gammaP L X Y := by
    rw [eval_relabel _ _ (baseW_isQ _ _ _ _ _) (by omega), baseW_eval]; rfl
  simp only [gadgetW]
  split_ifs
  · rw [Word.eval_inv _ (relabel_isQ hn L X Y), h]
  · exact h

theorem rectData (hn : 2 ≤ n) (X Y : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i)
    (hY : ∀ j ∈ Y, IsCol j) : RectData n (SOf X) (SOf Y) := by
  refine ⟨hn, ?_, ?_⟩
  · rintro l ⟨i, hi, rfl⟩
    have := hX i (Finset.mem_toList.1 hi)
    simp only [IsRow] at this
    simp only [layerZ]; omega
  · rintro l ⟨j, hj, rfl⟩
    have := hY j (Finset.mem_toList.1 hj)
    simp only [IsCol] at this
    simp only [layerZ]; omega

theorem gammaP_e (L : Letter) (X Y : Finset (Fin n)) (v : Sticker n) (k : Fin 24)
    (hb : ∀ t, baseC L.2.1 L.2.2.1 (SOf X) (SOf Y) (e v t) =
      e v (cycFn L.2.1 L.2.2.1 t)) :
    gammaP L X Y (e v k) = e v (lp (L.1, L.2.1, L.2.2.1, false) k) := by
  simp only [gammaP, Perm.mul_apply, actPerm_inv, actPerm_e, hb, cycFn_spec]
  rfl

/-- On an orbit of the rectangle, the gadget performs the letter's 3-cycle. -/
theorem gadget_on (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i)
    (hY : ∀ j ∈ Y, IsCol j) (i j : Fin n) (hi : i ∈ X) (hj : j ∈ Y) (k : Fin 24) :
    Word.eval (gadgetW hn L X Y) (e (rep i j) k) = e (rep i j) (lp L k) := by
  have hd := rectData hn X Y hX hY
  have hb : ∀ t, baseC L.2.1 L.2.2.1 (SOf X) (SOf Y) (e (rep i j) t) =
      e (rep i j) (cycFn L.2.1 L.2.2.1 t) := fun t =>
    baseC_on hd _ _ i j ((sOf_layer X i).2 hi) ((sOf_layer Y j).2 hj) t
  rw [gadgetW_eval]
  obtain ⟨τ, da, db, f⟩ := L
  cases f
  · simp only [Bool.false_eq_true, if_false]
    exact gammaP_e _ X Y _ k hb
  · simp only [if_true]
    rw [Perm.inv_eq_iff_eq]
    have := gammaP_e (τ, da, db, true) X Y (rep i j)
      ((cyc3 τ (mul τ (alphaOf da)) (mul τ (betaOf db)))⁻¹ k) hb
    simp only [lp, Bool.false_eq_true, if_false, if_true] at this ⊢
    rw [this, perm_apply_inv]

theorem gamma_fix {L : Letter} {X Y : Finset (Fin n)} {v : Sticker n} {k : Fin 24}
    (hb : ∀ t, baseC L.2.1 L.2.2.1 (SOf X) (SOf Y) (e v t) = e v t) (hn : 2 ≤ n) :
    Word.eval (gadgetW hn L X Y) (e v k) = e v k := by
  have hg : gammaP L X Y (e v k) = e v k := by
    simp only [gammaP, Perm.mul_apply, actPerm_inv, actPerm_e, hb]
    rw [← mul_assoc, mul_inv_self, zero_mul]
  rw [gadgetW_eval]
  split_ifs
  · rw [Perm.inv_eq_iff_eq]; exact hg.symm
  · exact hg

/-- The gadget fixes every other orbit (the partner orbits of the wings excepted). -/
theorem gadget_off (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i)
    (hY : ∀ j ∈ Y, IsCol j) (i j : Fin n) (hdom : InDom i j) (H1 : ¬ (i ∈ X ∧ j ∈ Y))
    (H2 : ¬ (i.val = 0 ∧ topI hn ∈ Y ∧ ∃ i' ∈ X, layerZ n i' = -layerZ n j)) (k : Fin 24) :
    Word.eval (gadgetW hn L X Y) (e (rep i j) k) = e (rep i j) k := by
  have hd := rectData hn X Y hX hY
  apply gamma_fix (fun t => baseC_off hd _ _ i j hdom ?_ ?_ t)
  · rw [sOf_layer, sOf_layer]; exact H1
  · rintro ⟨h0, hy, l, hl, hle⟩
    apply H2
    refine ⟨h0, ?_, l, Finset.mem_toList.1 hl, hle.symm⟩
    obtain ⟨t, ht, hte⟩ := hy
    have : layerZ n (topI hn) = layerZ n t := by
      rw [← hte]; simp only [layerZ, topI]; omega
    rw [layerZ_inj _ _ this]
    exact Finset.mem_toList.1 ht

/-- The gadget fixes the face centres. -/
theorem gadget_center (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i)
    (hY : ∀ j ∈ Y, IsCol j) (m : Fin n) (hm : layerZ n m = 0) (k : Fin 24) :
    Word.eval (gadgetW hn L X Y) (e (rep m m) k) = e (rep m m) k := by
  have hd := rectData hn X Y hX hY
  exact gamma_fix (fun t => baseC_center hd _ _ m hm t) hn

end RubiksGN
