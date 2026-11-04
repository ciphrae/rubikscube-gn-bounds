import RubiksGN.ChainSound

/-!
# The skeleton of a general cube: corners, middle edges, face centres

The corners and middle edges of an `n × n × n` cube behave exactly like those of the `3 × 3 × 3`
cube: the scaling map `ψ` carries the small model to the large cube, compatibly with the moves.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### Interpreting symbolic words -/

/-- The layer classification of a general cube. -/
def cls (n : ℕ) (i : Fin n) : Option (Fin 3) :=
  if i.val = 0 then some 0 else if i.val = n - 1 then some 2
  else if 2 * i.val + 1 = n then some 1 else none

/-- The layer of a general cube named by a symbol. -/
def layerOf (hn : 3 ≤ n) (c : Fin 3) : Fin n :=
  match c with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨(n - 1) / 2, by omega⟩
  | 2 => ⟨n - 1, by omega⟩

theorem layerOf_inj (hn : 3 ≤ n) (c c' : Fin 3) (h : layerOf hn c = layerOf hn c') : c = c' := by
  have h' := congrArg Fin.val h
  fin_cases c <;> fin_cases c' <;> simp [layerOf] at h' ⊢ <;> omega

/-- A symbolic move as a move of the general cube. -/
def interp (hn : 3 ≤ n) (s : Sym) : Move n := (s.1, layerOf hn s.2.1, dirTurn s.2.2)

theorem interp_isQ (hn : 3 ≤ n) (s : Sym) : IsQ (interp hn s) := isQ_dirTurn _ _ _

/-- A quarter move as a letter. -/
def toL (m : Move n) : Axis × Fin n × Bool := (m.1, m.2.1, decide (m.2.2 = .cw))

/-- The key of a move: axis and layer. -/
def keyM (m : Move n) : Axis × Fin n := (m.1, m.2.1)

/-- Every layer of every axis turns an even number of times. -/
def EvenW (w : Word n) : Prop := ∀ c : Axis × Fin n, Even ((w.map keyM).count c)

theorem EvenW.append {u v : Word n} (hu : EvenW u) (hv : EvenW v) : EvenW (u ++ v) := by
  intro c
  simp only [List.map_append, List.count_append]
  exact (hu c).add (hv c)

theorem evenS_append {u v : List Sym} (hu : evenS u = true) (hv : evenS v = true) :
    evenS (u ++ v) = true := by
  simp only [evenS, List.all_eq_true, beq_iff_eq, List.countP_append] at *
  intro s hs
  have h1 := hu s hs
  have h2 := hv s hs
  omega

theorem evenS_interp (hn : 3 ≤ n) (w : List Sym) (h : evenS w = true) :
    EvenW (w.map (interp hn)) := by
  rintro ⟨a, i⟩
  simp only [List.map_map]
  rw [List.count, List.countP_map]
  by_cases hi : ∃ c, layerOf hn c = i
  · obtain ⟨c, rfl⟩ := hi
    have hs := h
    simp only [evenS, List.all_eq_true, beq_iff_eq] at hs
    have := hs (a, c, true) (mem_allSyms _)
    have heq : (List.countP (fun s' => Sym.sameKey (a, c, true) s') w) =
        List.countP ((fun x => x == (a, layerOf hn c)) ∘ (keyM ∘ interp hn)) w := by
      apply List.countP_congr
      intro s _
      simp only [Sym.sameKey, Function.comp, keyM, interp, Bool.and_eq_true, beq_iff_eq,
        Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, by rw [← h2]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, (layerOf_inj hn _ _ h2).symm⟩
    rw [← heq]
    exact Nat.even_iff.2 this
  · have : List.countP ((fun x => x == (a, i)) ∘ (keyM ∘ interp hn)) w = 0 := by
      rw [List.countP_eq_zero]
      intro s _ hs
      simp only [Function.comp, keyM, interp, beq_iff_eq, Prod.mk.injEq] at hs
      exact hi ⟨_, hs.2⟩
    rw [this]
    exact Even.zero

theorem evenW_inv (u : Word n) (hu : EvenW u) : EvenW (Word.inv u) := by
  intro c
  have h : (Word.inv u).map keyM = (u.map keyM).reverse := by
    simp only [Word.inv, List.map_reverse, List.map_map]
    rfl
  rw [h, List.count_reverse]
  exact hu c

/-! ### A piece of the cube -/

/-- A family of stickers on which all moves act through `sp`. -/
structure Piece (n N : ℕ) (sp : Sym → Perm (Fin N)) where
  E : Fin N → Sticker n
  spec : ∀ (a : Axis) (i : Fin n) (f : Fin N),
    quarter n a i (E f) = E (Fp (cls n) sp (a, i, true) f)

section Piece

variable {N : ℕ} {sp : Sym → Perm (Fin N)} (P : Piece n N sp)
  (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹)

include hflip

theorem Fp_false (a : Axis) (i : Fin n) :
    Fp (cls n) sp (a, i, false) = (Fp (cls n) sp (a, i, true))⁻¹ := by
  simp only [Fp]
  cases cls n i with
  | none => simp
  | some c => exact hflip (a, c, true)

theorem Piece.move_spec (m : Move n) (hm : IsQ m) (f : Fin N) :
    m.toPerm (P.E f) = P.E (Fp (cls n) sp (toL m) f) := by
  obtain ⟨a, i, t⟩ := m
  cases t
  · exact P.spec a i f
  · exact absurd rfl hm
  · change (quarter n a i)⁻¹ (P.E f) = P.E (Fp (cls n) sp (a, i, false) f)
    rw [Fp_false hflip, Perm.inv_eq_iff_eq, P.spec, perm_apply_inv]

theorem Piece.word_spec (w : Word n) (hw : ∀ m ∈ w, IsQ m) (f : Fin N) :
    Word.eval w (P.E f) = P.E (((w.map toL).map (Fp (cls n) sp)).prod f) := by
  induction w generalizing f with
  | nil => simp
  | cons m t ih =>
    simp only [Word.eval_cons, Perm.mul_apply, List.map_cons, List.prod_cons]
    rw [ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)),
      P.move_spec hflip m (hw m List.mem_cons_self)]

end Piece

theorem toL_interp (hn : 3 ≤ n) (s : Sym) : toL (interp hn s) = (s.1, layerOf hn s.2.1, s.2.2) := by
  obtain ⟨a, c, d⟩ := s
  cases d <;> simp [toL, interp, dirTurn]

/-! ### Chain words acting on a piece -/

/-- What a passing chain check provides on a piece. -/
theorem piece_cancel {N : ℕ} (hN : N ≤ 32) {sp : Sym → Perm (Fin N)} {tab : List Tb}
    {ls : List Level} (hs : ∀ s, Rep (sp s) (tableOf tab s))
    (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹) (hchk : chainCheck N tab ls = true)
    (P : Piece n N sp) (Q : List Sym → Prop) (hQ0 : Q []) (hQa : ∀ u v, Q u → Q v → Q (u ++ v))
    (hQg : ∀ e ∈ gensOf ls, Q e.w) (a : Word n) (haQ : ∀ m ∈ a, IsQ m) (he : EvenW a) :
    ∃ w : List Sym, w.length ≤ boundOf ls ∧ Q w ∧ evalS sp w * ((a.map toL).map (Fp (cls n) sp)).prod = 1 := by
  have hmem := even_mem hN hs hflip hchk (cls n) (a.map toL) (by
    intro c
    have : (a.map toL).map (fun l => (l.1, l.2.1)) = a.map keyM := by
      simp only [List.map_map]; rfl
    rw [this]
    exact he c)
  obtain ⟨h1, h2⟩ := chk_closed hN hs hflip hchk
  have hinv := mem_InP h1 h2 _ (inv_mem hmem)
  obtain ⟨w, hw, hlen, hQw⟩ := word_of_InP Q hQ0 hQa ls hQg _ hinv
  exact ⟨w, hlen, hQw, by rw [hw]; simp⟩

/-! ### The scaling map -/

/-- Scaling from the `3 × 3 × 3` model to the `n × n × n` cube. -/
def psi (n : ℕ) (t : ℤ) : ℤ :=
  if t = 3 then n else if t = -3 then -(n : ℤ) else if t = 2 then (n : ℤ) - 1
  else if t = -2 then -((n : ℤ) - 1) else 0

theorem psi_neg (t : ℤ) : psi n (-t) = -psi n t := by
  simp only [psi]
  split_ifs <;> omega

set_option maxHeartbeats 4000000 in
theorem act_psi (k : Fin 24) (p q r : ℤ) :
    act k (psi n p, psi n q, psi n r) =
      (psi n (act k (p, q, r)).1, psi n (act k (p, q, r)).2.1, psi n (act k (p, q, r)).2.2) := by
  obtain ⟨k, hk⟩ := k
  interval_cases k <;> simp only [act, actN, psi_neg]

theorem coord_act_psi (a : Axis) (k : Fin 24) (p q r : ℤ) :
    a.coord (act k (psi n p, psi n q, psi n r)) = psi n (a.coord (act k (p, q, r))) := by
  rw [act_psi]
  cases a <;> rfl

/-- Coordinates occurring in the model. -/
def ValidT (t : ℤ) : Prop := t = 3 ∨ t = -3 ∨ t = 2 ∨ t = -2 ∨ t = 0

instance (t : ℤ) : Decidable (ValidT t) := by unfold ValidT; infer_instance

/-- The coordinate of a symbolic layer in the model. -/
def z3 : Fin 3 → ℤ
  | 0 => -2
  | 1 => 0
  | 2 => 2

theorem layerZ_of_cls (hn : 3 ≤ n) (i : Fin n) (c : Fin 3) (h : cls n i = some c) :
    layerZ n i = psi n (z3 c) := by
  simp only [cls] at h
  split_ifs at h with h0 h1 h2 <;> simp only [Option.some.injEq] at h <;> subst h <;>
    simp [z3, psi, layerZ] <;> omega

theorem clamp_psi (hn : 3 ≤ n) (t : ℤ) (ht : ValidT t) : clamp n (psi n t) = psi n (clamp 3 t) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [psi, clamp] <;> omega

theorem psi_z3_inj (hn : 3 ≤ n) (t : ℤ) (ht : t = 2 ∨ t = -2 ∨ t = 0) (c : Fin 3) :
    psi n t = psi n (z3 c) ↔ t = z3 c := by
  rcases ht with rfl | rfl | rfl <;> fin_cases c <;> simp [psi, z3] <;> omega

theorem clamp3_valid (t : ℤ) (ht : ValidT t) : clamp 3 t = 2 ∨ clamp 3 t = -2 ∨ clamp 3 t = 0 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [clamp]

theorem cls_none_ne (hn : 3 ≤ n) (i : Fin n) (h : cls n i = none) (t : ℤ)
    (ht : t = 2 ∨ t = -2 ∨ t = 0) : psi n t ≠ layerZ n i := by
  simp only [cls] at h
  split_ifs at h with h0 h1 h2
  have := i.isLt
  rcases ht with rfl | rfl | rfl <;> simp [psi, layerZ] <;> omega

/-- Left multiplication on orbit coordinates. -/
def lmulP (τ : Fin 24) : Perm (Fin 24) where
  toFun k := mul τ k
  invFun k := mul (inv τ) k
  left_inv k := by
    change mul (inv τ) (mul τ k) = k
    rw [← mul_assoc, inv_mul_self, zero_mul]
  right_inv k := by
    change mul τ (mul (inv τ) k) = k
    rw [← mul_assoc, mul_inv_self, zero_mul]

/-- A layer of the model acting on orbit coordinates. -/
def rvM (v : V) (a : Axis) (z : ℤ) : Perm (Fin 24) :=
  condPerm (lmulP (rx a)) (fun k => clamp 3 (a.coord (act k v)) = z) (fun k => by
    change clamp 3 (a.coord (act (mul (rx a) k) v)) = z ↔ _
    rw [act_mul, coord_rx])

/-- A symbolic move on orbit coordinates. -/
def spV (v : V) (s : Sym) : Perm (Fin 24) :=
  if s.2.2 then rvM v s.1 (z3 s.2.1) else (rvM v s.1 (z3 s.2.1))⁻¹

theorem spV_flip (v : V) (s : Sym) : spV v (Sym.flip s) = (spV v s)⁻¹ := by
  obtain ⟨a, c, d⟩ := s
  cases d <;> simp [spV, Sym.flip]

/-- The quarter turn on an orbit coordinate. -/
theorem quarter_e (a : Axis) (i : Fin n) (v : Sticker n) (k : Fin 24) :
    quarter n a i (e v k) =
      if clamp n (a.coord (act k v.1)) = layerZ n i then e v (mul (rx a) k) else e v k := by
  split_ifs with h
  · rw [quarter, slice_apply_of n a _ _ h, actPerm_e]
  · rw [quarter, slice_apply_not n a _ _ h]

/-- Pieces given by scaling an orbit of the model. -/
def scaledPiece (hn : 3 ≤ n) (p q r : ℤ) (v : Sticker n)
    (hv : v.1 = (psi n p, psi n q, psi n r))
    (hvalid : ∀ (k : Fin 24) (a : Axis), ValidT (a.coord (act k (p, q, r)))) :
    Piece n 24 (spV (p, q, r)) where
  E := e v
  spec := by
    intro a i k
    rw [quarter_e, hv, coord_act_psi, clamp_psi hn _ (hvalid k a)]
    have hc := clamp3_valid _ (hvalid k a)
    simp only [Fp]
    cases hcl : cls n i with
    | none =>
      rw [if_neg (fun h => cls_none_ne hn i hcl _ hc h)]
      rfl
    | some c =>
      rw [layerZ_of_cls hn i c hcl]
      simp only [psi_z3_inj hn _ hc c, spV, if_true]
      show _ = e v (condPerm _ _ _ k)
      rw [condPerm_apply]
      by_cases h : clamp 3 (a.coord (act k (p, q, r))) = z3 c
      · simp only [h, if_true]; rfl
      · simp only [h, if_false]

/-! ### Corners and middle edges -/

/-- Model coordinates of a corner sticker. -/
def vC : V := (-2, 2, 3)

/-- Model coordinates of a middle-edge sticker. -/
def vE : V := (-2, 0, 3)

theorem vC_valid : ∀ (k : Fin 24) (a : Axis), ValidT (a.coord (act k vC)) := by decide +kernel
theorem vE_valid : ∀ (k : Fin 24) (a : Axis), ValidT (a.coord (act k vE)) := by decide +kernel

theorem spC_rep' : ∀ (s : Sym) (i : Fin 24), ((spV vC s) i).val = getT (tableOf tabC s) i := by
  decide +kernel
theorem spE_rep' : ∀ (s : Sym) (i : Fin 24), ((spV vE s) i).val = getT (tableOf tabE s) i := by
  decide +kernel

theorem spC_mid : ∀ (a : Axis) (d : Bool) (i : Fin 24), spV vC (a, 1, d) i = i := by decide +kernel

/-- The corner layer. -/
def row0 (hn : 3 ≤ n) : Fin n := ⟨0, by omega⟩

theorem layerZ_row0 (hn : 3 ≤ n) : layerZ n (row0 hn) = psi n (-2) := by
  simp [row0, layerZ, psi]

theorem layerZ_layerOf2 (hn : 3 ≤ n) : layerZ n (layerOf hn 2) = psi n 2 := by
  simp [layerOf, layerZ, psi]; omega

/-- The top index as a layer, for `3 ≤ n`. -/
theorem topI_eq (hn : 3 ≤ n) : topI (by omega : 2 ≤ n) = layerOf hn 2 := rfl

/-- The corner piece. -/
def cornerP (hn : 3 ≤ n) : Piece n 24 (spV vC) :=
  scaledPiece hn (-2) 2 3 (rep (row0 hn) (layerOf hn 2))
    (by
      simp only [rep, layerZ_row0, layerZ_layerOf2]
      simp [psi])
    vC_valid

/-- For odd `n`: the middle layer. -/
theorem layerZ_mid (hn : 3 ≤ n) (hodd : n % 2 = 1) : layerZ n (layerOf hn 1) = 0 := by
  simp only [layerOf, layerZ]
  omega

/-- The middle-edge piece (odd `n`). -/
def edgeP (hn : 3 ≤ n) (hodd : n % 2 = 1) : Piece n 24 (spV vE) :=
  scaledPiece hn (-2) 0 3 (rep (row0 hn) (layerOf hn 1))
    (by
      simp only [rep, layerZ_row0, layerZ_mid hn hodd]
      simp [psi])
    vE_valid

/-! ### Face centres -/

/-- Unit vectors along the faces. -/
def faceVec : Fin 6 → V
  | 0 => (0, 0, 1)
  | 1 => (0, 0, -1)
  | 2 => (0, 1, 0)
  | 3 => (0, -1, 0)
  | 4 => (1, 0, 0)
  | 5 => (-1, 0, 0)

/-- The index of a unit vector. -/
def faceIdx (v : V) : Fin 6 :=
  if v.2.2 = 1 then 0 else if v.2.2 = -1 then 1 else if v.2.1 = 1 then 2
  else if v.2.1 = -1 then 3 else if v.1 = 1 then 4 else 5

/-- The action of rotations on faces. -/
def faceAct (τ : Fin 24) (f : Fin 6) : Fin 6 := faceIdx (act τ (faceVec f))

theorem act_faceVec : ∀ (τ : Fin 24) (f : Fin 6), act τ (faceVec f) = faceVec (faceAct τ f) := by
  decide +kernel

theorem faceAct_inv : ∀ (τ : Fin 24) (f : Fin 6), faceAct (inv τ) (faceAct τ f) = f := by
  decide +kernel

theorem faceAct_inv' : ∀ (τ : Fin 24) (f : Fin 6), faceAct τ (faceAct (inv τ) f) = f := by
  decide +kernel

/-- The action on faces as a permutation. -/
def faceP (τ : Fin 24) : Perm (Fin 6) := ⟨faceAct τ, faceAct (inv τ), faceAct_inv τ, faceAct_inv' τ⟩

theorem coord_faceAct : ∀ (a : Axis) (f : Fin 6),
    a.coord (faceVec (faceAct (rx a) f)) = a.coord (faceVec f) := by
  decide +kernel

/-- The middle layer about an axis acting on faces. -/
def zRot (a : Axis) : Perm (Fin 6) :=
  condPerm (faceP (rx a)) (fun f => a.coord (faceVec f) = 0) (fun f => by
    change a.coord (faceVec (faceAct (rx a) f)) = 0 ↔ _
    rw [coord_faceAct])

/-- Symbolic moves acting on the faces: only the middle layers move the face centres. -/
def spZ (s : Sym) : Perm (Fin 6) :=
  if s.2.1 = 1 then (if s.2.2 then zRot s.1 else (zRot s.1)⁻¹) else 1

theorem spZ_flip (s : Sym) : spZ (Sym.flip s) = (spZ s)⁻¹ := by
  obtain ⟨a, c, d⟩ := s
  simp only [spZ, Sym.flip]
  by_cases hc : c = 1
  · cases d <;> simp [hc]
  · simp [hc]

theorem spZ_rep' : ∀ (s : Sym) (i : Fin 6), ((spZ s) i).val = getT (tableOf tabZ s) i := by
  decide +kernel

/-- The face-centre sticker of a face (odd `n`). -/
def centerS (hodd : n % 2 = 1) (f : Fin 6) : Sticker n :=
  ⟨((n : ℤ) * (faceVec f).1, (n : ℤ) * (faceVec f).2.1, (n : ℤ) * (faceVec f).2.2), by
    have h0 : IsCoord n 0 := by simp only [IsCoord]; omega
    fin_cases f <;> simp [faceVec, IsSticker, h0]⟩

theorem act_scale (τ : Fin 24) (N : ℤ) (u : V) :
    act τ (N * u.1, N * u.2.1, N * u.2.2) =
      (N * (act τ u).1, N * (act τ u).2.1, N * (act τ u).2.2) := by
  obtain ⟨x, y, z⟩ := u
  simp only [act_linear, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem actPerm_centerS (hodd : n % 2 = 1) (τ : Fin 24) (f : Fin 6) :
    actPerm n τ (centerS hodd f) = centerS hodd (faceAct τ f) := by
  apply Subtype.ext
  change act τ _ = _
  simp only [centerS]
  rw [act_scale, act_faceVec]

theorem axis_face_cases : ∀ (a : Axis) (f : Fin 6),
    a.coord (faceVec f) = 0 ∨ (faceAct (rx a) f = f ∧
      (a.coord (faceVec f) = 1 ∨ a.coord (faceVec f) = -1)) := by
  decide +kernel

theorem coord_center (hodd : n % 2 = 1) (a : Axis) (f : Fin 6) :
    a.coord (centerS hodd f).1 = (n : ℤ) * a.coord (faceVec f) := by
  cases a <;> rfl

theorem cls_some1_iff (hn : 3 ≤ n) (i : Fin n) : cls n i = some 1 ↔ layerZ n i = 0 := by
  have := i.isLt
  simp only [cls, layerZ]
  split_ifs <;> simp <;> omega

/-- The face-centre piece (odd `n`). -/
def centerP (hn : 3 ≤ n) (hodd : n % 2 = 1) : Piece n 6 spZ where
  E := centerS hodd
  spec := by
    intro a i f
    have hFp : Fp (cls n) spZ (a, i, true) f =
        if cls n i = some 1 then zRot a f else f := by
      simp only [Fp]
      cases h : cls n i with
      | none => simp
      | some c =>
        by_cases hc : c = 1
        · subst hc; simp [spZ]
        · have : (some c : Option (Fin 3)) ≠ some 1 := by simpa using hc
          simp [spZ, hc]
    rw [hFp]
    have hn0 : clamp n 0 = 0 := clamp_of_ne 0 (by omega) (by omega)
    rcases axis_face_cases a f with h0 | ⟨hfix, h1⟩
    · by_cases hl : layerZ n i = 0
      · rw [if_pos ((cls_some1_iff hn i).2 hl), quarter, slice_apply_of n a _ _ (by
          rw [coord_center, h0, Int.mul_zero, hn0, hl])]
        rw [actPerm_centerS]
        congr 1
        change _ = condPerm _ _ _ f
        rw [condPerm_apply, if_pos h0]
        rfl
      · rw [if_neg (fun h => hl ((cls_some1_iff hn i).1 h)), quarter, slice_apply_not n a _ _ (by
          rw [coord_center, h0, Int.mul_zero, hn0]
          exact fun h => hl h.symm)]
    · have hz : zRot a f = f := by
        change condPerm _ _ _ f = f
        rw [condPerm_apply, if_neg]
        rcases h1 with h1 | h1 <;> rw [h1] <;> decide
      have hq : quarter n a i (centerS hodd f) = centerS hodd f := by
        by_cases hc : clamp n (a.coord (centerS hodd f).1) = layerZ n i
        · rw [quarter, slice_apply_of n a _ _ hc, actPerm_centerS, hfix]
        · rw [quarter, slice_apply_not n a _ _ hc]
      rw [hq]
      split_ifs
      · rw [hz]
      · rfl

/-! ### The chains on a general cube -/

theorem cls_layerOf0 (hn : 3 ≤ n) : cls n (layerOf hn 0) = some 0 := by
  simp [cls, layerOf]

theorem cls_layerOf2 (hn : 3 ≤ n) : cls n (layerOf hn 2) = some 2 := by
  have hv : (layerOf hn 2).val = n - 1 := rfl
  rw [cls, if_neg (by rw [hv]; omega), if_pos hv]

theorem cls_layerOf1 (hn : 3 ≤ n) (hodd : n % 2 = 1) : cls n (layerOf hn 1) = some 1 := by
  have hv : (layerOf hn 1).val = (n - 1) / 2 := rfl
  rw [cls, if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_pos (by rw [hv]; omega)]

theorem cls_layerOf1_even (hn : 3 ≤ n) (heven : n % 2 = 0) : cls n (layerOf hn 1) = none := by
  have hv : (layerOf hn 1).val = (n - 1) / 2 := rfl
  rw [cls, if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega), if_neg (by rw [hv]; omega)]

/-- The symbolic layer of `layerOf` is recovered, for odd `n`. -/
theorem Fp_interp_odd {N : ℕ} (sp : Sym → Perm (Fin N)) (hn : 3 ≤ n) (hodd : n % 2 = 1) (s : Sym) :
    Fp (cls n) sp (toL (interp hn s)) = sp s := by
  obtain ⟨a, c, d⟩ := s
  rw [toL_interp]
  simp only [Fp]
  have : cls n (layerOf hn c) = some c := by
    fin_cases c
    · exact cls_layerOf0 hn
    · exact cls_layerOf1 hn hodd
    · exact cls_layerOf2 hn
  rw [this]

theorem Fp_interp_corner (hn : 3 ≤ n) (s : Sym) :
    Fp (cls n) (spV vC) (toL (interp hn s)) = spV vC s := by
  by_cases hodd : n % 2 = 1
  · exact Fp_interp_odd _ hn hodd s
  · obtain ⟨a, c, d⟩ := s
    rw [toL_interp]
    simp only [Fp]
    have hm : ∀ c : Fin 3, (cls n (layerOf hn c) = some c) ∨ c = 1 := by
      intro c
      fin_cases c
      · exact Or.inl (cls_layerOf0 hn)
      · exact Or.inr rfl
      · exact Or.inl (cls_layerOf2 hn)
    rcases hm c with h | rfl
    · rw [h]
    · rw [cls_layerOf1_even hn (by omega)]
      apply Equiv.ext
      intro i
      exact (spC_mid a d i).symm

/-- A symbolic word on a piece, through `interp`. -/
theorem piece_interp {N : ℕ} {sp : Sym → Perm (Fin N)} (P : Piece n N sp)
    (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹) (hn : 3 ≤ n)
    (hF : ∀ s, Fp (cls n) sp (toL (interp hn s)) = sp s) (w : List Sym) (f : Fin N) :
    Word.eval (w.map (interp hn)) (P.E f) = P.E (evalS sp w f) := by
  rw [P.word_spec hflip _ (fun m hm => by
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 hm
    exact interp_isQ hn s)]
  congr 2
  simp only [List.map_map, evalS]
  congr 1
  apply List.map_congr_left
  intro s _
  exact hF s

theorem rep_of_table {N : ℕ} {sp : Sym → Perm (Fin N)} {tab : List Tb}
    (h : ∀ (s : Sym) (i : Fin N), ((sp s) i).val = getT (tableOf tab s) i) :
    ∀ s, Rep (sp s) (tableOf tab s) := fun s i => h s i

/-- The purity data of a chain word. -/
def PureW {N₁ N₂ : ℕ} (s₁ : Sym → Perm (Fin N₁)) (s₂ : Sym → Perm (Fin N₂)) (w : List Sym) : Prop :=
  evenS w = true ∧ evalS s₁ w = 1 ∧ evalS s₂ w = 1

theorem PureW.nil {N₁ N₂ : ℕ} (s₁ : Sym → Perm (Fin N₁)) (s₂ : Sym → Perm (Fin N₂)) :
    PureW s₁ s₂ [] := ⟨by decide, rfl, rfl⟩

theorem PureW.append {N₁ N₂ : ℕ} (s₁ : Sym → Perm (Fin N₁)) (s₂ : Sym → Perm (Fin N₂))
    (u v : List Sym) (hu : PureW s₁ s₂ u) (hv : PureW s₁ s₂ v) : PureW s₁ s₂ (u ++ v) := by
  refine ⟨evenS_append hu.1 hv.1, ?_, ?_⟩
  · have h1 := hu.2.1
    have h2 := hv.2.1
    simp only [evalS, List.map_append, List.prod_append] at *
    rw [h1, h2, one_mul]
  · have h1 := hu.2.2
    have h2 := hv.2.2
    simp only [evalS, List.map_append, List.prod_append] at *
    rw [h1, h2, one_mul]

theorem pure_of_check {N₁ N₂ : ℕ} (h1 : N₁ ≤ 32) (h2 : N₂ ≤ 32) {s₁ : Sym → Perm (Fin N₁)}
    {s₂ : Sym → Perm (Fin N₂)} {t₁ t₂ : List Tb} (r₁ : ∀ s, Rep (s₁ s) (tableOf t₁ s))
    (r₂ : ∀ s, Rep (s₂ s) (tableOf t₂ s)) {ls : List Level}
    (hp : pureOK [(N₁, t₁), (N₂, t₂)] ls = true) : ∀ e ∈ gensOf ls, PureW s₁ s₂ e.w := by
  intro e he
  simp only [pureOK, List.all_eq_true] at hp
  have h := hp e he
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, beq_iff_eq] at h
  obtain ⟨he', hA, hB⟩ := h
  refine ⟨he', ?_, ?_⟩
  · have hr := tbOf_rep h1 r₁ e.w
    rw [hA] at hr
    exact hr.ext (rep_one h1)
  · have hr := tbOf_rep h2 r₂ e.w
    rw [hB] at hr
    exact hr.ext (rep_one h2)

theorem interp_prop (hn : 3 ≤ n) (w : List Sym) :
    (∀ m ∈ w.map (interp hn), IsQ m) ∧ (w.map (interp hn)).length = w.length := by
  refine ⟨fun m hm => ?_, by simp⟩
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 hm
  exact interp_isQ hn s

/-- Cancel the corners of an even word by a short even word pure on the rest of the skeleton. -/
theorem corner_cancel (hn : 3 ≤ n) (a : Word n) (haQ : ∀ m ∈ a, IsQ m) (he : EvenW a) :
    ∃ w : List Sym, w.length ≤ 170 ∧ evenS w = true ∧ evalS (spV vE) w = 1 ∧ evalS spZ w = 1 ∧
      ∀ k, Word.eval (w.map (interp hn)) (Word.eval a ((cornerP hn).E k)) = (cornerP hn).E k := by
  have hr := rep_of_table spC_rep'
  have hE := rep_of_table spE_rep'
  have hZ := rep_of_table spZ_rep'
  obtain ⟨w, hlen, hQ, hw⟩ := piece_cancel (by norm_num) hr (spV_flip vC) cChain_ok (cornerP hn)
    (PureW (spV vE) spZ) (PureW.nil _ _) (PureW.append _ _)
    (pure_of_check (by norm_num) (by norm_num) hE hZ cChain_pure) a haQ he
  refine ⟨w, by rw [cChain_bound] at hlen; exact hlen, hQ.1, hQ.2.1, hQ.2.2, fun k => ?_⟩
  rw [(cornerP hn).word_spec (spV_flip vC) a haQ,
    piece_interp _ (spV_flip vC) hn (Fp_interp_corner hn)]
  rw [← Perm.mul_apply, hw]
  rfl

theorem edge_cancel (hn : 3 ≤ n) (hodd : n % 2 = 1) (a : Word n) (haQ : ∀ m ∈ a, IsQ m)
    (he : EvenW a) :
    ∃ w : List Sym, w.length ≤ 220 ∧ evenS w = true ∧ evalS (spV vC) w = 1 ∧ evalS spZ w = 1 ∧
      ∀ k, Word.eval (w.map (interp hn)) (Word.eval a ((edgeP hn hodd).E k)) = (edgeP hn hodd).E k := by
  have hr := rep_of_table spE_rep'
  have hC := rep_of_table spC_rep'
  have hZ := rep_of_table spZ_rep'
  obtain ⟨w, hlen, hQ, hw⟩ := piece_cancel (by norm_num) hr (spV_flip vE) eChain_ok (edgeP hn hodd)
    (PureW (spV vC) spZ) (PureW.nil _ _) (PureW.append _ _)
    (pure_of_check (by norm_num) (by norm_num) hC hZ eChain_pure) a haQ he
  refine ⟨w, by rw [eChain_bound] at hlen; exact hlen, hQ.1, hQ.2.1, hQ.2.2, fun k => ?_⟩
  rw [(edgeP hn hodd).word_spec (spV_flip vE) a haQ,
    piece_interp _ (spV_flip vE) hn (Fp_interp_odd _ hn hodd)]
  rw [← Perm.mul_apply, hw]
  rfl

theorem center_cancel (hn : 3 ≤ n) (hodd : n % 2 = 1) (a : Word n) (haQ : ∀ m ∈ a, IsQ m)
    (he : EvenW a) :
    ∃ w : List Sym, w.length ≤ 16 ∧ evenS w = true ∧ evalS (spV vC) w = 1 ∧ evalS (spV vE) w = 1 ∧
      ∀ f, Word.eval (w.map (interp hn)) (Word.eval a ((centerP hn hodd).E f)) = (centerP hn hodd).E f := by
  have hr := rep_of_table spZ_rep'
  have hC := rep_of_table spC_rep'
  have hE := rep_of_table spE_rep'
  obtain ⟨w, hlen, hQ, hw⟩ := piece_cancel (by norm_num) hr spZ_flip zChain_ok (centerP hn hodd)
    (PureW (spV vC) (spV vE)) (PureW.nil _ _) (PureW.append _ _)
    (pure_of_check (by norm_num) (by norm_num) hC hE zChain_pure) a haQ he
  refine ⟨w, by rw [zChain_bound] at hlen; exact hlen, hQ.1, hQ.2.1, hQ.2.2, fun k => ?_⟩
  rw [(centerP hn hodd).word_spec spZ_flip a haQ,
    piece_interp _ spZ_flip hn (Fp_interp_odd _ hn hodd)]
  rw [← Perm.mul_apply, hw]
  rfl

end RubiksGN
