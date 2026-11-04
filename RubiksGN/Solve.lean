import RubiksGN.Skeleton
import RubiksGN.Parallel

/-!
# Solving every position

For every `s ≥ 1`, every element of the cube group is solved by at most
`3n + 406 + 275 * phaseCost (n/2 - 1) (n - n/2) s` quarter turns.
-/

open Equiv

namespace RubiksGN

open Classical

variable {n : ℕ}

/-! ### Words for group elements -/

theorem word_of_mem (g : Perm (Sticker n)) (hg : g ∈ cubeGroup n) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ Word.eval w = g := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨a, i, t⟩, rfl⟩ := hy
    cases t
    · exact ⟨[(a, i, .cw)], by simp [IsQ], by simp⟩
    · exact ⟨[(a, i, .cw), (a, i, .cw)], by simp [IsQ], by simp [Move.toPerm]⟩
    · exact ⟨[(a, i, .ccw)], by simp [IsQ], by simp⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul x y _ _ ix iy =>
    obtain ⟨u, hu, rfl⟩ := ix
    obtain ⟨v, hv, rfl⟩ := iy
    refine ⟨u ++ v, ?_, by simp⟩
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hu m h
    · exact hv m h
  | inv x _ ix =>
    obtain ⟨u, hu, rfl⟩ := ix
    exact ⟨Word.inv u, Word.inv_isQ u hu, Word.eval_inv u hu⟩

/-! ### The action on a general orbit, and its sign -/

/-- One layer acting on the coordinates of an orbit. -/
noncomputable def rvG (v : Sticker n) (a : Axis) (i : Fin n) : Perm (Fin 24) :=
  condPerm (lmulP (rx a)) (fun k => clamp n (a.coord (act k v.1)) = layerZ n i) (fun k => by
    change clamp n (a.coord (act (mul (rx a) k) v.1)) = _ ↔ _
    rw [act_mul, coord_rx])

/-- A move acting on the coordinates of an orbit. -/
noncomputable def rvL (v : Sticker n) (m : Move n) : Perm (Fin 24) :=
  if m.2.2 = .cw then rvG v m.1 m.2.1 else (rvG v m.1 m.2.1)⁻¹

/-- A word acting on the coordinates of an orbit. -/
noncomputable def Rv (v : Sticker n) (w : Word n) : Perm (Fin 24) := (w.map (rvL v)).prod

theorem quarter_rvG (v : Sticker n) (a : Axis) (i : Fin n) (k : Fin 24) :
    quarter n a i (e v k) = e v (rvG v a i k) := by
  rw [quarter_e]
  simp only [rvG]
  rw [condPerm_apply]
  split_ifs <;> rfl

theorem move_rvL (v : Sticker n) (m : Move n) (hm : IsQ m) (k : Fin 24) :
    m.toPerm (e v k) = e v (rvL v m k) := by
  obtain ⟨a, i, t⟩ := m
  cases t
  · exact quarter_rvG v a i k
  · exact absurd rfl hm
  · change (quarter n a i)⁻¹ (e v k) = e v ((rvG v a i)⁻¹ k)
    rw [Perm.inv_eq_iff_eq, quarter_rvG, perm_apply_inv]

theorem word_Rv (v : Sticker n) (w : Word n) (hw : ∀ m ∈ w, IsQ m) (k : Fin 24) :
    Word.eval w (e v k) = e v (Rv v w k) := by
  induction w generalizing k with
  | nil => rfl
  | cons m t ih =>
    simp only [Word.eval_cons, Perm.mul_apply, Rv, List.map_cons, List.prod_cons]
    rw [ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)), move_rvL v m (hw m List.mem_cons_self)]
    rfl

/-- A word with even layer counts acts on each orbit by an even permutation. -/
theorem sign_Rv (v : Sticker n) (w : Word n) (he : EvenW w) : Perm.sign (Rv v w) = 1 := by
  have hs : ∀ m m' : Move n, keyM m = keyM m' →
      Perm.sign (rvL v m) * Perm.sign (rvL v m') = 1 := by
    intro m m' hk
    have hval : ∀ x : Move n, Perm.sign (rvL v x) = Perm.sign (rvG v x.1 x.2.1) := by
      intro x
      simp only [rvL]
      split_ifs <;> simp
    simp only [keyM, Prod.mk.injEq] at hk
    rw [hval, hval, hk.1, hk.2]
    exact Int.units_mul_self _
  have := even_word_mem (fun m : Move n => Perm.sign (rvL v m)) keyM (⊥ : Subgroup ℤˣ)
    (fun l l' hk => by rw [Subgroup.mem_bot]; exact hs l l' hk)
    (fun l l' => by
      rw [Subgroup.mem_bot, mul_comm (Perm.sign (rvL v l))]
      group)
    (fun l k hk => by
      rw [Subgroup.mem_bot] at hk ⊢
      simp [hk])
    (fun l => ⟨l, by rw [Int.units_inv_eq_self], rfl⟩) _ w rfl he
  rw [Subgroup.mem_bot] at this
  simp only [Rv]
  rw [map_list_prod, List.map_map]
  exact this

/-! ### Classifying the stickers -/

theorem act2 (x y z : ℤ) : act 2 (x, y, z) = (z, y, -x) := rfl
theorem act3 (x y z : ℤ) : act 3 (x, y, z) = (-y, x, z) := rfl
theorem act4 (x y z : ℤ) : act 4 (x, y, z) = (x, -y, -z) := rfl
theorem act10 (x y z : ℤ) : act 10 (x, y, z) = (-x, -y, z) := rfl
theorem act11 (x y z : ℤ) : act 11 (x, y, z) = (x, z, -y) := rfl
theorem act19 (x y z : ℤ) : act 19 (x, y, z) = (y, -x, z) := rfl

theorem exists_top (hn : 3 ≤ n) (q : Sticker n) :
    ∃ τ : Fin 24, ∃ a b : ℤ, IsCoord n a ∧ IsCoord n b ∧ (actPerm n τ q).1 = (a, b, (n : ℤ)) := by
  obtain ⟨⟨x, y, z⟩, hs⟩ := q
  simp only [IsSticker] at hs
  rcases hs with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
  · rcases hx with rfl | rfl
    · exact ⟨17, -z, y, (isCoord_neg n z).2 hz, hy, rfl⟩
    · exact ⟨2, z, y, hz, hy, by simp only [actPerm_val]; rw [act2, neg_neg]⟩
  · rcases hy with rfl | rfl
    · exact ⟨1, x, -z, hx, (isCoord_neg n z).2 hz, rfl⟩
    · exact ⟨11, x, z, hx, hz, by simp only [actPerm_val]; rw [act11, neg_neg]⟩
  · rcases hz with rfl | rfl
    · exact ⟨0, x, y, hx, hy, rfl⟩
    · exact ⟨4, x, -y, hx, (isCoord_neg n y).2 hy, by simp only [actPerm_val]; rw [act4, neg_neg]⟩

/-- Every sticker lies in the orbit of a representative in the domain, or of a face centre. -/
theorem classify (hn : 3 ≤ n) (q : Sticker n) :
    ∃ k : Fin 24, (∃ i j : Fin n, InDom i j ∧ q = e (rep i j) k) ∨
      (∃ m : Fin n, layerZ n m = 0 ∧ q = e (rep m m) k) := by
  obtain ⟨τ, a, b, ha, hb, hq⟩ := exists_top hn q
  have hq' : q = actPerm n (inv τ) (actPerm n τ q) := by
    apply Subtype.ext
    simp [act_inv_act]
  have top : ∀ (a' b' : ℤ) (t : Fin 24), IsCoord n a' → IsCoord n b' →
      act t (a', b', (n : ℤ)) = (a, b, (n : ℤ)) → a' < 0 → 0 ≤ b' →
      ∃ k : Fin 24, (∃ i j : Fin n, InDom i j ∧ q = e (rep i j) k) ∨
        (∃ m : Fin n, layerZ n m = 0 ∧ q = e (rep m m) k) := by
    intro a' b' t h1 h2 hact h3 h4
    obtain ⟨i, rfl⟩ := exists_layer h1
    obtain ⟨j, rfl⟩ := exists_layer h2
    refine ⟨mul (inv τ) t, Or.inl ⟨i, j, ⟨h3, h4⟩, ?_⟩⟩
    rw [hq', ← actPerm_e]
    congr 1
    apply Subtype.ext
    rw [hq]
    exact hact.symm
  by_cases h1 : a < 0
  · by_cases h2 : 0 ≤ b
    · exact top a b 0 ha hb rfl h1 h2
    · exact top b (-a) 3 hb ((isCoord_neg n a).2 ha) (by rw [act3, neg_neg]) (by omega) (by omega)
  · by_cases h3 : a = 0
    · subst h3
      by_cases h4 : b < 0
      · exact top b (-0) 3 hb ((isCoord_neg n 0).2 ha) (by rw [act3, neg_neg]) (by omega) (by omega)
      · by_cases h5 : b = 0
        · subst h5
          obtain ⟨m, hm⟩ := exists_layer ha
          refine ⟨inv τ, Or.inr ⟨m, hm, ?_⟩⟩
          rw [hq']
          congr 1
          apply Subtype.ext
          rw [hq]
          simp [rep, hm]
        · exact top (-b) 0 19 ((isCoord_neg n b).2 hb) ha (by rw [act19, neg_neg]) (by omega) (by omega)
    · by_cases h4 : b ≤ 0
      · exact top (-a) (-b) 10 ((isCoord_neg n a).2 ha) ((isCoord_neg n b).2 hb)
          (by rw [act10, neg_neg, neg_neg]) (by omega) (by omega)
      · exact top (-b) a 19 ((isCoord_neg n b).2 hb) ha (by rw [act19, neg_neg]) (by omega) (by omega)

/-! ### Rigidity of the cubies -/

/-- The cubie carrying a sticker. -/
def cub (n : ℕ) (v : V) : V := (clamp n v.1, clamp n v.2.1, clamp n v.2.2)

set_option maxHeartbeats 4000000 in
theorem cub_act (hn : 0 < n) (τ : Fin 24) (v : V) : cub n (act τ v) = act τ (cub n v) := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨k, hk⟩ := τ
  interval_cases k <;> simp only [act, actN, cub, clamp_neg _ hn]

theorem coord_cub (a : Axis) (v : V) : a.coord (cub n v) = clamp n (a.coord v) := by
  cases a <;> rfl

theorem cub_slice (hn : 0 < n) (a : Axis) (S : ℤ → Prop) (q q' : Sticker n) (h : cub n q.1 = cub n q'.1) :
    cub n (slice n a S q).1 = cub n (slice n a S q').1 := by
  have hc : clamp n (a.coord q.1) = clamp n (a.coord q'.1) := by
    rw [← coord_cub, ← coord_cub, h]
  by_cases hS : S (clamp n (a.coord q.1))
  · rw [slice_apply_of n a S q hS, slice_apply_of n a S q' (hc ▸ hS)]
    simp only [actPerm_val, cub_act hn, h]
  · rw [slice_apply_not n a S q hS, slice_apply_not n a S q' (hc ▸ hS)]
    exact h

theorem cub_slice_inv (hn : 0 < n) (a : Axis) (S : ℤ → Prop) (q q' : Sticker n)
    (h : cub n q.1 = cub n q'.1) :
    cub n ((slice n a S)⁻¹ q).1 = cub n ((slice n a S)⁻¹ q').1 := by
  have hc : clamp n (a.coord q.1) = clamp n (a.coord q'.1) := by
    rw [← coord_cub, ← coord_cub, h]
  by_cases hS : S (clamp n (a.coord q.1))
  · rw [slice_inv_apply_of n a S q hS, slice_inv_apply_of n a S q' (hc ▸ hS)]
    simp only [actPerm_inv_val, cub_act hn, h]
  · rw [slice_inv_apply_not n a S q hS, slice_inv_apply_not n a S q' (hc ▸ hS)]
    exact h

theorem cub_word (hn : 0 < n) (w : Word n) (hw : ∀ m ∈ w, IsQ m) (q q' : Sticker n)
    (h : cub n q.1 = cub n q'.1) :
    cub n (Word.eval w q).1 = cub n (Word.eval w q').1 := by
  induction w with
  | nil => simpa using h
  | cons m t ih =>
    have h1 := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    simp only [Word.eval_cons, Perm.mul_apply]
    obtain ⟨a, i, tt⟩ := m
    cases tt
    · exact cub_slice hn a (· = layerZ n i) _ _ h1
    · exact absurd rfl (hw _ List.mem_cons_self)
    · exact cub_slice_inv hn a (· = layerZ n i) _ _ h1

theorem cubie_two (hn : 3 ≤ n) (X Y Z y : ℤ) (hs : IsSticker n (X, Y, Z))
    (h1 : clamp n X = -((n : ℤ) - 1)) (h2 : clamp n Y = y) (h3 : clamp n Z = (n : ℤ) - 1)
    (hy1 : y < (n : ℤ) - 1) (hy2 : -((n : ℤ) - 1) < y) :
    (X, Y, Z) = (-((n : ℤ) - 1), y, (n : ℤ)) ∨ (X, Y, Z) = (-(n : ℤ), y, (n : ℤ) - 1) := by
  simp only [IsSticker, IsCoord] at hs
  simp only [clamp] at h1 h2 h3
  simp only [Prod.mk.injEq]
  split_ifs at h1 h2 h3 <;> omega

/-- The rotation carrying a wing representative to the partner sticker. -/
def kappa2 : Fin 24 := 23

theorem act_kappa2 (a b c : ℤ) : act kappa2 (a, b, c) = (-c, -a, b) := rfl

/-- A word fixing the row orbit of a wing fixes the rigidly attached partner orbit. -/
theorem partner_fixed (hn : 3 ≤ n) (w : Word n) (hw : ∀ m ∈ w, IsQ m) (j i' : Fin n) (k : Fin 24)
    (hj1 : 0 < layerZ n j) (hj2 : layerZ n j < (n : ℤ) - 1) (hi' : layerZ n i' = -layerZ n j)
    (hfix : Word.eval w (e (rep i' (layerOf hn 2)) (mul k kappa2)) =
      e (rep i' (layerOf hn 2)) (mul k kappa2)) :
    Word.eval w (e (rep (row0 hn) j) k) = e (rep (row0 hn) j) k := by
  have hn0 : 0 < n := by omega
  set y := layerZ n j with hy
  have htop : layerZ n (layerOf hn 2) = (n : ℤ) - 1 := by
    rw [layerZ_layerOf2]; simp [psi]
  have hz : layerZ n (row0 hn) = -((n : ℤ) - 1) := by
    rw [layerZ_row0]; simp [psi]
  have hq' : (e (rep (row0 hn) j) k).1 = act k (-((n : ℤ) - 1), y, (n : ℤ)) := by
    simp only [e, actPerm_val, rep, hz, ← hy]
  have hq0 : (e (rep i' (layerOf hn 2)) (mul k kappa2)).1 = act k (-(n : ℤ), y, (n : ℤ) - 1) := by
    simp only [e, actPerm_val, rep, act_mul, htop, hi', act_kappa2, neg_neg, ← hy]
  have hclamp : clamp n y = y := clamp_of_ne y (by omega) (by omega)
  have hc1 : clamp n (-(n : ℤ)) = -((n : ℤ) - 1) := by simp [clamp]; omega
  have hc2 : clamp n (-((n : ℤ) - 1)) = -((n : ℤ) - 1) := clamp_of_ne _ (by omega) (by omega)
  have hc3 : clamp n ((n : ℤ) - 1) = (n : ℤ) - 1 := clamp_of_ne _ (by omega) (by omega)
  have hc4 : clamp n (n : ℤ) = (n : ℤ) - 1 := by simp [clamp]
  have hsame : cub n (e (rep (row0 hn) j) k).1 = cub n (e (rep i' (layerOf hn 2)) (mul k kappa2)).1 := by
    rw [hq', hq0, cub_act hn0, cub_act hn0]
    simp only [cub, hclamp, hc1, hc2, hc3, hc4]
  have hne : e (rep (row0 hn) j) k ≠ e (rep i' (layerOf hn 2)) (mul k kappa2) := by
    intro h
    have := congrArg Subtype.val h
    rw [hq', hq0] at this
    have h2 := congrArg (act (inv k)) this
    rw [act_inv_act, act_inv_act] at h2
    simp only [Prod.mk.injEq] at h2
    omega
  have hcw := cub_word hn0 w hw _ _ hsame
  rw [hfix, ← hsame, hq', cub_act hn0] at hcw
  set r := Word.eval w (e (rep (row0 hn) j) k) with hr
  have hs' : IsSticker n (act (inv k) r.1) := act_isSticker n _ r.2
  have hcub : cub n (act (inv k) r.1) = cub n (-((n : ℤ) - 1), y, (n : ℤ)) := by
    rw [cub_act hn0, hcw, act_inv_act]
  obtain ⟨X, Y, Z⟩ : V := act (inv k) r.1 |> fun v => v
  have hcases : act (inv k) r.1 = (-((n : ℤ) - 1), y, (n : ℤ)) ∨
      act (inv k) r.1 = (-(n : ℤ), y, (n : ℤ) - 1) := by
    generalize act (inv k) r.1 = u at hs' hcub
    obtain ⟨A, B, C⟩ := u
    simp only [cub, hclamp, hc2, hc4, Prod.mk.injEq] at hcub
    exact cubie_two hn A B C y hs' hcub.1 hcub.2.1 hcub.2.2 hj2 (by omega)
  rcases hcases with h | h
  · apply Subtype.ext
    rw [hq', ← h, act_act_inv]
  · exfalso
    apply hne
    apply (Word.eval w).injective
    rw [hfix]
    apply Subtype.ext
    rw [hq0, ← h, act_act_inv]

/-! ### The skeleton step -/

theorem layerZ_eq_mid (hn : 3 ≤ n) (j : Fin n) (hj : layerZ n j = 0) :
    n % 2 = 1 ∧ j = layerOf hn 1 := by
  have := j.isLt
  simp only [layerZ] at hj
  refine ⟨by omega, ?_⟩
  apply Fin.ext
  have hv : (layerOf hn 1).val = (n - 1) / 2 := rfl
  rw [hv]
  omega

theorem center_e (hn : 3 ≤ n) (hodd : n % 2 = 1) (k : Fin 24) :
    e (rep (layerOf hn 1) (layerOf hn 1)) k = (centerP hn hodd).E (faceAct k 0) := by
  apply Subtype.ext
  change act k (layerZ n (layerOf hn 1), layerZ n (layerOf hn 1), (n : ℤ)) = _
  rw [layerZ_mid hn hodd]
  have h := act_scale k (n : ℤ) (faceVec 0)
  rw [act_faceVec] at h
  have e0 : ((n : ℤ) * (faceVec 0).1, (n : ℤ) * (faceVec 0).2.1, (n : ℤ) * (faceVec 0).2.2) =
      (0, 0, (n : ℤ)) := by simp [faceVec]
  rw [e0] at h
  exact h

theorem piece_fix {N : ℕ} {sp : Sym → Perm (Fin N)} (P : Piece n N sp)
    (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹) (hn : 3 ≤ n)
    (hF : ∀ s, Fp (cls n) sp (toL (interp hn s)) = sp s) (w : List Sym) (h : evalS sp w = 1)
    (f : Fin N) : Word.eval (w.map (interp hn)) (P.E f) = P.E f := by
  rw [piece_interp P hflip hn hF, h]
  rfl

/-- The skeleton step: a short even word cancels an even word on the skeleton. -/
theorem skel_word (hn : 3 ≤ n) (a : Word n) (haQ : ∀ m ∈ a, IsQ m) (he : EvenW a) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧ W.length ≤ 406 ∧ EvenW W ∧
      (∀ k, Word.eval W (Word.eval a (e (rep (row0 hn) (layerOf hn 2)) k)) =
        e (rep (row0 hn) (layerOf hn 2)) k) ∧
      (∀ j : Fin n, layerZ n j = 0 → ∀ k, Word.eval W (Word.eval a (e (rep (row0 hn) j) k)) =
        e (rep (row0 hn) j) k) ∧
      (∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval W (Word.eval a (e (rep m m) k)) =
        e (rep m m) k) := by
  by_cases hodd : n % 2 = 1
  · obtain ⟨wc, cl, ce, cE, cZ, cC⟩ := corner_cancel hn a haQ he
    obtain ⟨we, el, ee, eC, eZ, eE⟩ := edge_cancel hn hodd a haQ he
    obtain ⟨wz, zl, ze, zC, zE, zZ⟩ := center_cancel hn hodd a haQ he
    have hFC := Fp_interp_corner hn
    have hFE := Fp_interp_odd (spV vE) hn hodd
    have hFZ := Fp_interp_odd spZ hn hodd
    have hEa : ∀ k, Word.eval a ((edgeP hn hodd).E k) ∈ Set.range (edgeP hn hodd).E := fun k =>
      ⟨_, ((edgeP hn hodd).word_spec (spV_flip vE) a haQ k).symm⟩
    have hCa : ∀ k, Word.eval a ((cornerP hn).E k) ∈ Set.range (cornerP hn).E := fun k =>
      ⟨_, ((cornerP hn).word_spec (spV_flip vC) a haQ k).symm⟩
    have hZa : ∀ k, Word.eval a ((centerP hn hodd).E k) ∈ Set.range (centerP hn hodd).E := fun k =>
      ⟨_, ((centerP hn hodd).word_spec spZ_flip a haQ k).symm⟩
    refine ⟨wc.map (interp hn) ++ (we.map (interp hn) ++ wz.map (interp hn)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩ <;> exact interp_isQ hn s
    · simp only [List.length_append, List.length_map]; omega
    · exact (evenS_interp hn wc ce).append ((evenS_interp hn we ee).append (evenS_interp hn wz ze))
    · intro k
      simp only [Word.eval_append, Perm.mul_apply]
      obtain ⟨x, hx⟩ := hCa k
      change Word.eval (wc.map (interp hn)) (Word.eval (we.map (interp hn))
        (Word.eval (wz.map (interp hn)) (Word.eval a ((cornerP hn).E k)))) = (cornerP hn).E k
      rw [← hx, piece_fix _ (spV_flip vC) hn hFC _ zC, piece_fix _ (spV_flip vC) hn hFC _ eC, hx]
      exact cC k
    · intro j hj k
      obtain ⟨_, rfl⟩ := layerZ_eq_mid hn j hj
      simp only [Word.eval_append, Perm.mul_apply]
      obtain ⟨x, hx⟩ := hEa k
      change Word.eval (wc.map (interp hn)) (Word.eval (we.map (interp hn))
        (Word.eval (wz.map (interp hn)) (Word.eval a ((edgeP hn hodd).E k)))) = (edgeP hn hodd).E k
      rw [← hx, piece_fix _ (spV_flip vE) hn hFE _ zE, hx, eE k,
        piece_fix _ (spV_flip vE) hn hFE _ cE]
    · intro m hm k
      obtain ⟨_, rfl⟩ := layerZ_eq_mid hn m hm
      simp only [Word.eval_append, Perm.mul_apply]
      rw [center_e hn hodd]
      rw [zZ, piece_fix _ spZ_flip hn hFZ _ eZ, piece_fix _ spZ_flip hn hFZ _ cZ]
  · obtain ⟨wc, cl, ce, _, _, cC⟩ := corner_cancel hn a haQ he
    refine ⟨wc.map (interp hn), ?_, ?_, evenS_interp hn wc ce, cC, ?_, ?_⟩
    · intro m hm
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 hm
      exact interp_isQ hn s
    · simp only [List.length_map]; omega
    · intro j hj
      exact absurd (layerZ_eq_mid hn j hj).1 hodd
    · intro m hm
      exact absurd (layerZ_eq_mid hn m hm).1 hodd

/-! ### Rows and columns -/

/-- The rows of the cover. -/
def rowsF (n : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => 0 < i.val ∧ 2 * i.val + 1 < n

/-- The columns of the cover. -/
def colsF (n : ℕ) : Finset (Fin n) := Finset.univ.filter fun j => n ≤ 2 * j.val + 1

theorem card_fin_range (lo hi : ℕ) (hhi : hi ≤ n) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ i, P i ↔ lo ≤ i.val ∧ i.val < hi) :
    (Finset.univ.filter P).card = hi - lo := by
  have : (Finset.univ.filter P).map Fin.valEmbedding = Finset.Ico lo hi := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico, hP]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]

theorem card_rowsF : (rowsF n).card = n / 2 - 1 := by
  apply card_fin_range 1 (n / 2) (by omega)
  intro i
  omega

theorem card_colsF : (colsF n).card = n - n / 2 := by
  apply card_fin_range (n / 2) n le_rfl
  intro i
  have := i.isLt
  omega

/-- The total number of quarter turns. -/
def upperW (n s : ℕ) : ℕ :=
  3 * n + 406 + 275 * phaseCost (n / 2 - 1) (n - n / 2) s

/-- **The upper bound, parametrised.** Every position is solved in `upperW n s` quarter turns. -/
theorem solve (hn : 3 ≤ n) (s : ℕ) (hs : 0 < s) (g : Perm (Sticker n)) (hg : g ∈ cubeGroup n) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ upperW n s ∧ Word.eval w * g = 1 := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨w₀, hw₀, rfl⟩ := word_of_mem g hg
  -- parity repair
  let K : Finset (Axis × Fin n) := Finset.univ.filter fun c => Odd ((w₀.map keyM).count c)
  let u : Word n := K.toList.map fun c => (c.1, c.2, Turn.cw)
  have huQ : ∀ m ∈ u, IsQ m := by
    intro m hm
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hm
    simp [IsQ]
  have hulen : u.length ≤ 3 * n := by
    have h1 : u.length = K.card := by simp [u]
    have h2 : K.card ≤ Fintype.card (Axis × Fin n) := Finset.card_le_univ _
    have h3 : Fintype.card (Axis × Fin n) = 3 * n := by
      rw [Fintype.card_prod, Fintype.card_fin]
      rfl
    omega
  let a : Word n := Word.inv u ++ w₀
  have haQ : ∀ m ∈ a, IsQ m := by
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact Word.inv_isQ u huQ m h
    · exact hw₀ m h
  have ha : EvenW a := by
    intro c
    have h1 : ((Word.inv u).map keyM).count c = (u.map keyM).count c := by
      have : (Word.inv u).map keyM = (u.map keyM).reverse := by
        simp only [Word.inv, List.map_reverse, List.map_map]
        rfl
      rw [this, List.count_reverse]
    have h2 : u.map keyM = K.toList := by
      simp only [u, List.map_map]
      conv_rhs => rw [← List.map_id K.toList]
      rfl
    simp only [a, List.map_append, List.count_append, h1, h2]
    rw [(Finset.nodup_toList K).count]
    by_cases hc : Odd ((w₀.map keyM).count c)
    · have hm : c ∈ K.toList := by
        rw [Finset.mem_toList]
        simp [K, hc]
      rw [if_pos hm]
      exact Odd.add_odd odd_one hc
    · have hm : c ∉ K.toList := by
        rw [Finset.mem_toList]
        simp [K, hc]
      rw [if_neg hm, zero_add]
      exact Nat.not_odd_iff_even.1 hc
  -- skeleton
  obtain ⟨Ws, hsQ, hslen, hsE, hC, hE, hZ⟩ := skel_word hn a haQ ha
  let a₁ : Word n := Ws ++ a
  have ha₁Q : ∀ m ∈ a₁, IsQ m := by
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hsQ m h
    · exact haQ m h
  have ha₁E : EvenW a₁ := hsE.append ha
  -- rows and columns
  have hR : ∀ i ∈ rowsF n, IsRow i := fun i hi => (Finset.mem_filter.1 hi).2
  have hCol : ∀ j ∈ colsF n, IsCol j := fun j hj => (Finset.mem_filter.1 hj).2
  have huniv : ∀ i j : Fin n, ∃ S : List Letter, S.Sublist uSeq ∧
      prodL S = (Rv (rep i j) a₁)⁻¹ := fun i j =>
    universal _ (by rw [Perm.sign_inv]; exact sign_Rv _ _ ha₁E)
  choose S hS1 hS2 using huniv
  obtain ⟨Wp, hpQ, hplen, hpF, hpA⟩ := parallel_seq hn2 hR hCol s hs uSeq S
    (fun i _ j _ => hS1 i j)
  rw [uSeq_length, card_rowsF, card_colsF] at hplen
  refine ⟨Wp ++ (Ws ++ Word.inv u), ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hpQ m h
    · rcases List.mem_append.1 h with h | h
      · exact hsQ m h
      · exact Word.inv_isQ u huQ m h
  · simp only [List.length_append, Word.inv_length, upperW]
    omega
  · let W : Word n := Wp ++ a₁
    have hWQ : ∀ m ∈ W, IsQ m := by
      intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact hpQ m h
      · exact ha₁Q m h
    have hval : Word.eval (Wp ++ (Ws ++ Word.inv u)) * Word.eval w₀ = Word.eval W := by
      simp only [W, a₁, a, Word.eval_append, _root_.mul_assoc]
    rw [hval]
    have hrow : ∀ i j : Fin n, IsRow i → IsCol j → ∀ k,
        Word.eval W (e (rep i j) k) = e (rep i j) k := by
      intro i j hi hj k
      simp only [W, Word.eval_append, Perm.mul_apply]
      rw [word_Rv _ a₁ ha₁Q, hpA i (by simp [rowsF, IsRow] at hi ⊢; omega) j
        (by simp [colsF, IsCol] at hj ⊢; omega), hS2]
      simp
    have hskel1 : ∀ k, Word.eval W (e (rep (row0 hn) (layerOf hn 2)) k) =
        e (rep (row0 hn) (layerOf hn 2)) k := by
      intro k
      simp only [W, a₁, Word.eval_append, Perm.mul_apply]
      rw [hC k]
      exact hpF.1 (layerOf hn 2) (Or.inl rfl) k
    have hskel2 : ∀ j : Fin n, layerZ n j = 0 → ∀ k, Word.eval W (e (rep (row0 hn) j) k) =
        e (rep (row0 hn) j) k := by
      intro j hj k
      simp only [W, a₁, Word.eval_append, Perm.mul_apply]
      rw [hE j hj k]
      exact hpF.1 j (Or.inr hj) k
    have hskel3 : ∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval W (e (rep m m) k) =
        e (rep m m) k := by
      intro m hm k
      simp only [W, a₁, Word.eval_append, Perm.mul_apply]
      rw [hZ m hm k]
      exact hpF.2 m hm k
    apply Equiv.ext
    intro q
    rw [Perm.one_apply]
    obtain ⟨k, ⟨i, j, hd, rfl⟩ | ⟨m, hm, rfl⟩⟩ := classify hn q
    · have hd1 := hd.1
      have hd2 := hd.2
      simp only [layerZ] at hd1 hd2
      have hjlt := j.isLt
      by_cases hi0 : i.val = 0
      · have hie : i = row0 hn := Fin.ext hi0
        subst hie
        by_cases htop : j = layerOf hn 2
        · subst htop
          exact hskel1 k
        · by_cases hz : layerZ n j = 0
          · exact hskel2 j hz k
          · have hjv : j.val ≠ n - 1 := fun h => htop (Fin.ext h)
            have hc : IsCoord n (-layerZ n j) := (isCoord_neg n _).2 (layerZ_isCoord j)
            obtain ⟨i', hi'⟩ := exists_layer hc
            have hpos : 0 < layerZ n j := by
              have : 0 ≤ layerZ n j := hd.2
              omega
            have hlt : layerZ n j < (n : ℤ) - 1 := by
              simp only [layerZ]; omega
            apply partner_fixed hn W hWQ j i' k hpos hlt hi'
            apply hrow
            · have hb := i'.isLt
              simp only [layerZ] at hi' hpos hlt
              simp only [IsRow]
              omega
            · simp only [IsCol, layerOf]; omega
      · apply hrow
        · simp only [IsRow]; omega
        · simp only [IsCol]; omega
    · exact hskel3 m hm k

end RubiksGN
