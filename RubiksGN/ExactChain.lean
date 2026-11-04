import RubiksGN.Rounds
import RubiksGN.ExactData

/-!
# The exact universal lists

`exact_universal`: for all even `π₁ π₂`, one template per list of `exactLists` has `∏ eT = π₁` and `∏ eM = π₂`.

The check `xChainOK` runs through the levels of `exactLevels`, in the order of `scripts/check_exact_chain.py`. To keep the kernel
away from products of permutations, every letter is a list giving a 4-cycle, and only the images of the support of the column
under a template are computed: conjugating a cycle gives the cycle of the images (`conj_cyc`). So `eT t` and `eM t` act through the
recorded cycles `c`, `D` (`etF`, `emF`).
-/

open Equiv

namespace RubiksGN

/-! ### Cycles as lists -/

/-- The action of the 4-cycle `a ↦ b ↦ c ↦ d ↦ a`. -/
def cyc : List (Fin 24) → Fin 24 → Fin 24
  | [a, b, c, d], x =>
    if x = a then b else if x = b then c else if x = c then d else if x = d then a else x
  | _, x => x

theorem cyc_map (g : Perm (Fin 24)) (a b c d x : Fin 24) :
    cyc [g a, g b, g c, g d] (g x) = g (cyc [a, b, c, d] x) := by
  simp only [cyc, g.injective.eq_iff]
  split_ifs <;> rfl

/-- Conjugating a cycle gives the cycle of the images. -/
theorem conj_cyc (g K : Perm (Fin 24)) (a b c d : Fin 24) (hK : ∀ x, K x = cyc [a, b, c, d] x)
    (y : Fin 24) : (g * K * g⁻¹) y = cyc [g a, g b, g c, g d] y := by
  obtain ⟨x, rfl⟩ := g.surjective y
  simp [Perm.mul_apply, hK, cyc_map]

/-- The cycle of a face letter. -/
def faceC : TLet → List (Fin 24)
  | (.x, true, true) => [2, 6, 15, 22]
  | (.x, true, false) => [2, 22, 15, 6]
  | (.x, false, true) => [12, 20, 17, 23]
  | (.x, false, false) => [12, 23, 17, 20]
  | (.y, true, true) => [8, 16, 21, 11]
  | (.y, true, false) => [8, 11, 21, 16]
  | (.y, false, true) => [1, 5, 14, 9]
  | (.y, false, false) => [1, 9, 14, 5]
  | (.z, true, true) => [0, 3, 10, 19]
  | (.z, true, false) => [0, 19, 10, 3]
  | (.z, false, true) => [4, 13, 7, 18]
  | (.z, false, false) => [4, 18, 7, 13]

/-- The cycle of a row letter on the target orbit. -/
def rowTC : TLet → List (Fin 24)
  | (.x, true, true) => [7, 16, 10, 14]
  | (.x, true, false) => [7, 14, 10, 16]
  | (.x, false, true) => [0, 1, 4, 11]
  | (.x, false, false) => [0, 11, 4, 1]
  | (.y, true, true) => [18, 23, 19, 22]
  | (.y, true, false) => [18, 22, 19, 23]
  | (.y, false, true) => [3, 6, 13, 20]
  | (.y, false, false) => [3, 20, 13, 6]
  | (.z, true, true) => [2, 8, 12, 5]
  | (.z, true, false) => [2, 5, 12, 8]
  | (.z, false, true) => [9, 15, 21, 17]
  | (.z, false, false) => [9, 17, 21, 15]

/-- The cycle of a row letter on the mirror orbit. -/
def rowMC : TLet → List (Fin 24)
  | (.x, true, true) => [5, 13, 21, 19]
  | (.x, true, false) => [5, 19, 21, 13]
  | (.x, false, true) => [3, 9, 18, 8]
  | (.x, false, false) => [3, 8, 18, 9]
  | (.y, true, true) => [0, 2, 7, 17]
  | (.y, true, false) => [0, 17, 7, 2]
  | (.y, false, true) => [4, 12, 10, 15]
  | (.y, false, false) => [4, 15, 10, 12]
  | (.z, true, true) => [1, 6, 16, 23]
  | (.z, true, false) => [1, 23, 16, 6]
  | (.z, false, true) => [11, 20, 14, 22]
  | (.z, false, false) => [11, 22, 14, 20]

theorem faceA_cyc : ∀ (l : TLet) (k : Fin 24), faceA l k = cyc (faceC l) k := by decide +kernel
theorem rowT_cyc : ∀ (l : TLet) (k : Fin 24), rowT l k = cyc (rowTC l) k := by decide +kernel
theorem rowM_cyc : ∀ (l : TLet) (k : Fin 24), rowM l k = cyc (rowMC l) k := by decide +kernel
theorem colK_cyc : ∀ k : Fin 24, colK k = cyc [5, 13, 21, 19] k := by decide +kernel
theorem colM_cyc : ∀ k : Fin 24, colM k = cyc [7, 16, 10, 14] k := by decide +kernel
theorem colK_inv_cyc : ∀ k : Fin 24, colK⁻¹ k = cyc [5, 19, 21, 13] k := by decide +kernel
theorem colM_inv_cyc : ∀ k : Fin 24, colM⁻¹ k = cyc [7, 14, 10, 16] k := by decide +kernel

/-! ### Fast evaluation of templates -/

/-- `faceVal f x`. -/
def faceF : List TLet → Fin 24 → Fin 24
  | [], x => x
  | l :: f, x => cyc (faceC l) (faceF f x)

/-- `(faceVal f)⁻¹ x`. -/
def faceInvF : List TLet → Fin 24 → Fin 24
  | [], x => x
  | l :: f, x => faceInvF f (cyc (faceC (l.1, l.2.1, !l.2.2)) x)

/-- A piece at a point, for given cycles of the row letters. -/
def pieceF (row : TLet → List (Fin 24)) (p : TPiece) (x : Fin 24) : Fin 24 :=
  faceF p.f (cyc (row p.r) (faceInvF p.f x))

/-- A template at a point, for given cycles of the row letters. -/
def tmplF (row : TLet → List (Fin 24)) : Tmpl → Fin 24 → Fin 24
  | [], x => x
  | p :: τ, x => pieceF row p (tmplF row τ x)

theorem faceVal_apply (f : List TLet) (x : Fin 24) : faceVal f x = faceF f x := by
  induction f with
  | nil => rfl
  | cons l f ih =>
    change (faceA l * faceVal f) x = _
    rw [Perm.mul_apply, ih, faceA_cyc, faceF]

theorem faceA_inv (l : TLet) : (faceA l)⁻¹ = faceA (l.1, l.2.1, !l.2.2) := by
  simp [faceA, dpow_not]

theorem faceVal_inv_apply (f : List TLet) (x : Fin 24) : (faceVal f)⁻¹ x = faceInvF f x := by
  induction f generalizing x with
  | nil => rfl
  | cons l f ih =>
    change (faceA l * faceVal f)⁻¹ x = _
    rw [_root_.mul_inv_rev, Perm.mul_apply, ih, faceA_inv, faceA_cyc, faceInvF]

theorem piece_apply (R : TLet → Perm (Fin 24)) (row : TLet → List (Fin 24))
    (hR : ∀ l k, R l k = cyc (row l) k) (p : TPiece) (x : Fin 24) :
    (faceVal p.f * R p.r * (faceVal p.f)⁻¹) x = pieceF row p x := by
  simp only [Perm.mul_apply, faceVal_inv_apply, hR, faceVal_apply, pieceF]

theorem evalT_apply (τ : Tmpl) (x : Fin 24) : evalT τ x = tmplF rowTC τ x := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    change (pieceT p * evalT τ) x = _
    rw [Perm.mul_apply, ih, tmplF]
    exact piece_apply rowT rowTC rowT_cyc p _

theorem evalTm_apply (τ : Tmpl) (x : Fin 24) : evalTm τ x = tmplF rowMC τ x := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    change (pieceTm p * evalTm τ) x = _
    rw [Perm.mul_apply, ih, tmplF]
    exact piece_apply rowM rowMC rowM_cyc p _

/-! ### The elements act through the recorded cycles -/

/-- `eT` of an entry at a point. -/
def etF (ε : ExactEntry) (x : Fin 24) : Fin 24 := cyc ε.c (cyc [5, 19, 21, 13] x)

/-- `eM` of an entry at a point. -/
def emF (ε : ExactEntry) (x : Fin 24) : Fin 24 := cyc ε.D (cyc [7, 14, 10, 16] x)

/-- `c` is a cycle of the images of `a, b, d, e` under `g`, from any starting point. -/
def rotOK (c : List (Fin 24)) (g : Fin 24 → Fin 24) (a b d e : Fin 24) : Bool :=
  decide (c = [g a, g b, g d, g e] ∨ c = [g b, g d, g e, g a] ∨ c = [g d, g e, g a, g b] ∨
    c = [g e, g a, g b, g d])

theorem cyc_rot (a b c d x : Fin 24) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    cyc [b, c, d, a] x = cyc [a, b, c, d] x := by
  simp only [cyc]
  split_ifs <;> simp_all

theorem cyc_of_rotOK (c : List (Fin 24)) (g : Perm (Fin 24)) (a b d e : Fin 24) (hab : a ≠ b)
    (had : a ≠ d) (hae : a ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (h : rotOK c g a b d e = true) (x : Fin 24) : cyc c x = cyc [g a, g b, g d, g e] x := by
  have i : ∀ {u v : Fin 24}, u ≠ v → g u ≠ g v := fun huv => g.injective.ne huv
  have r1 := cyc_rot (g a) (g b) (g d) (g e) x (i hab) (i had) (i hae)
  have r2 := cyc_rot (g b) (g d) (g e) (g a) x (i hbd) (i hbe) (i hab.symm)
  have r3 := cyc_rot (g d) (g e) (g a) (g b) x (i hde) (i had.symm) (i hbd.symm)
  simp only [rotOK, decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact r1
  · exact r2.trans r1
  · exact r3.trans (r2.trans r1)

theorem eT_apply_of (ε : ExactEntry)
    (h : rotOK ε.c (tmplF rowTC ε.tmpl) 5 13 21 19 = true) (x : Fin 24) :
    eT ε.tmpl x = etF ε x := by
  have hg : tmplF rowTC ε.tmpl = ⇑(evalT ε.tmpl) := funext fun y => (evalT_apply _ y).symm
  rw [hg] at h
  rw [etF, cyc_of_rotOK _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) h, ← colK_inv_cyc, ← conj_cyc _ colK _ _ _ _ colK_cyc]
  simp only [eT, conjT, Perm.mul_apply, dpow_true]

theorem eM_apply_of (ε : ExactEntry)
    (h : rotOK ε.D (tmplF rowMC ε.tmpl) 7 16 10 14 = true) (x : Fin 24) :
    eM ε.tmpl x = emF ε x := by
  have hg : tmplF rowMC ε.tmpl = ⇑(evalTm ε.tmpl) := funext fun y => (evalTm_apply _ y).symm
  rw [hg] at h
  rw [emF, cyc_of_rotOK _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) h, ← colM_inv_cyc, ← conj_cyc _ colM _ _ _ _ colM_cyc]
  simp only [eM, conjM, Perm.mul_apply, dpow_true]

private theorem units_comm (a b : ℤˣ) : a * b * a⁻¹ * b⁻¹ = 1 := by
  revert a b
  decide

/-- Every `eT` is even: it is a commutator. -/
theorem sign_eT (τ : Tmpl) : Perm.sign (eT τ) = 1 := by
  simp only [eT, conjT, dpow_true, map_mul, map_inv]
  exact units_comm _ _

/-- Every `eM` is even: it is a commutator. -/
theorem sign_eM (τ : Tmpl) : Perm.sign (eM τ) = 1 := by
  simp only [eM, conjM, dpow_true, map_mul, map_inv]
  exact units_comm _ _

/-! ### An even permutation fixing all but two points -/

/-- `even_last` of `RubiksGN/Universal.lean`, for any two points. -/
theorem even_of_two (fixed : List (Fin 24)) (a b : Fin 24) (hne : a ≠ b)
    (h : ∀ x : Fin 24, x ∈ fixed ∨ x = a ∨ x = b) (π : Perm (Fin 24))
    (hs : Perm.sign π = 1) (hf : ∀ f ∈ fixed, π f = f) : π = 1 := by
  have key : ∀ x y, π x = y → y ∈ fixed → x = y := fun x y hxy hy =>
    π.injective (by rw [hxy, hf y hy])
  have hA : π a = a := by
    by_contra hna
    have hy : π a = b := by
      rcases h (π a) with hy | hy | hy
      · exact absurd (key _ _ rfl hy).symm hna
      · exact absurd hy hna
      · exact hy
    have hb : π b = a := by
      rcases h (π b) with hz | hz | hz
      · have := (key _ _ rfl hz).symm
        exact absurd (π.injective (hy.trans this.symm)) hne
      · exact hz
      · exact absurd (π.injective (hy.trans hz.symm)) hne
    have hsw : π = swap a b := by
      apply Equiv.ext
      intro x
      rcases h x with hx | rfl | rfl
      · rw [hf x hx, swap_apply_of_ne_of_ne]
        · rintro rfl
          exact hna (hf _ hx)
        · rintro rfl
          exact hne (hb.symm.trans (hf _ hx))
      · rw [hy, swap_apply_left]
      · rw [hb, swap_apply_right]
    rw [hsw, Perm.sign_swap hne] at hs
    exact absurd hs (by decide)
  have hB : π b = b := by
    rcases h (π b) with hz | hz | hz
    · exact (key _ _ rfl hz).symm
    · exact absurd (π.injective (hz.trans hA.symm)) hne.symm
    · exact hz
  apply Equiv.ext
  intro x
  rw [Perm.one_apply]
  rcases h x with hx | rfl | rfl
  · exact hf x hx
  · exact hA
  · exact hB

/-! ### The check -/

/-- An entry: the recorded cycles are right, `eT` fixes `F` and `eM` fixes `P`. -/
def xEntryOK (F P : List (Fin 24)) (ε : ExactEntry) : Bool :=
  rotOK ε.c (tmplF rowTC ε.tmpl) 5 13 21 19 && rotOK ε.D (tmplF rowMC ε.tmpl) 7 16 10 14 &&
  F.all (fun f => decide (etF ε f = f)) && P.all (fun p => decide (emF ε p = p))

/-- A chain level with base point `b`, on the chain whose placed points are `G`. -/
def xLevelOK (main : ExactEntry → Fin 24 → Fin 24) (G F P : List (Fin 24)) (l : ExactLevel)
    (b : Fin 24) : Bool :=
  l.entries.all (xEntryOK F P) && !G.contains b &&
  (List.finRange 24).all fun x => G.contains x || l.entries.any fun ε => decide (main ε b = x)

/-- The table has a witness for the images `u, v, w` of `p0, p1, p2`. -/
def xWitnessOK (main : ExactEntry → Fin 24 → Fin 24) (lX lY : ExactLevel)
    (tab : List (List (Fin 24) × ℕ × ℕ)) (p0 p1 p2 u v w : Fin 24) : Bool :=
  match tab.lookup [u, v, w] with
  | some (i, j) =>
    match lX.entries[i]?, lY.entries[j]? with
    | some X, some Y =>
      decide (main X (main Y p0) = u) && decide (main X (main Y p1) = v) &&
        decide (main X (main Y p2) = w)
    | _, _ => false
  | none => false

/-- The two lists of a final factorization: all triples of distinct points are reached. -/
def xFinalOK (main : ExactEntry → Fin 24 → Fin 24) (G F P : List (Fin 24)) (lX lY : ExactLevel)
    (tab : List (List (Fin 24) × ℕ × ℕ)) : Bool :=
  lX.entries.all (xEntryOK F P) && lY.entries.all (xEntryOK F P) &&
  match lX.omega with
  | [p0, p1, p2, a, b] =>
    decide (a ≠ b) && decide (p0 ≠ p1) && decide (p0 ≠ p2) && decide (p1 ≠ p2) &&
    !G.contains p0 && !G.contains p1 && !G.contains p2 &&
    (List.finRange 24).all (fun x => G.contains x || lX.omega.contains x) &&
    lX.omega.all fun u => lX.omega.all fun v => lX.omega.all fun w =>
      decide (u = v) || decide (u = w) || decide (v = w) ||
        xWitnessOK main lX lY tab p0 p1 p2 u v w
  | _ => false

/-- The check of a whole chain, with `F` and `P` the points placed so far. -/
def xChainOK : List (Fin 24) → List (Fin 24) → List ExactLevel → Bool
  | F, P, [] => (List.finRange 24).all fun x => F.contains x && P.contains x
  | _, _, [_] => false
  | F, P, l :: l₂ :: ls =>
    match l.kind, l.base with
    | .T, [b] => xLevelOK etF F F P l b && xChainOK (b :: F) P (l₂ :: ls)
    | .M, [b] => xLevelOK emF P F P l b && xChainOK F (b :: P) (l₂ :: ls)
    | .TX, _ => xFinalOK etF F F P l l₂ exactTableT && xChainOK (l.omega ++ F) P ls
    | .MX, _ => xFinalOK emF P F P l l₂ exactTableM && xChainOK F (l.omega ++ P) ls
    | _, _ => false

/-- **The check of the data.** -/
theorem exactChain_ok : xChainOK [] [] exactLevels = true := by decide +kernel

/-! ### Soundness -/

/-- What the state of the check says about the two remaining permutations. -/
structure XInv (F P : List (Fin 24)) (π₁ π₂ : Perm (Fin 24)) : Prop where
  s₁ : Perm.sign π₁ = 1
  s₂ : Perm.sign π₂ = 1
  f₁ : ∀ f ∈ F, π₁ f = f
  f₂ : ∀ p ∈ P, π₂ p = p

/-- The facts behind `xEntryOK`. -/
theorem xEntryOK_sound {F P : List (Fin 24)} {ε : ExactEntry} (h : xEntryOK F P ε = true) :
    (∀ x, eT ε.tmpl x = etF ε x) ∧ (∀ x, eM ε.tmpl x = emF ε x) ∧ (∀ f ∈ F, eT ε.tmpl f = f) ∧
      (∀ p ∈ P, eM ε.tmpl p = p) := by
  simp only [xEntryOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have a1 := eT_apply_of ε h1
  have a2 := eM_apply_of ε h2
  exact ⟨a1, a2, fun f hf => (a1 f).trans (h3 f hf), fun p hp => (a2 p).trans (h4 p hp)⟩

theorem image_not_mem {G : List (Fin 24)} {π : Perm (Fin 24)} (hf : ∀ g ∈ G, π g = g) {b : Fin 24}
    (hb : b ∉ G) : π b ∉ G := by
  intro hm
  have := π.injective (hf _ hm)
  exact hb (this ▸ hm)

/-- A chain level has an entry for the image of the base point. -/
theorem xLevelOK_sound {main : ExactEntry → Fin 24 → Fin 24} {G F P : List (Fin 24)} {l : ExactLevel}
    {b : Fin 24} (h : xLevelOK main G F P l b = true) {π : Perm (Fin 24)} (hf : ∀ g ∈ G, π g = g) :
    b ∉ G ∧ ∃ ε ∈ l.entries, xEntryOK F P ε = true ∧ main ε b = π b := by
  simp only [xLevelOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.mem_finRange,
    true_implies, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hb : b ∉ G := fun hm => by
    rw [List.contains_iff_mem.2 hm] at h2
    exact absurd h2 (by decide)
  refine ⟨hb, ?_⟩
  rcases h3 (π b) with hm | ⟨ε, hε, he⟩
  · exact absurd (List.contains_iff_mem.1 hm) (image_not_mem hf hb)
  · exact ⟨ε, hε, h1 ε hε, he⟩

theorem xWitnessOK_sound {main : ExactEntry → Fin 24 → Fin 24} {lX lY : ExactLevel}
    {tab : List (List (Fin 24) × ℕ × ℕ)} {p0 p1 p2 u v w : Fin 24}
    (h : xWitnessOK main lX lY tab p0 p1 p2 u v w = true) :
    ∃ X ∈ lX.entries, ∃ Y ∈ lY.entries, main X (main Y p0) = u ∧ main X (main Y p1) = v ∧
      main X (main Y p2) = w := by
  unfold xWitnessOK at h
  split at h
  · split at h
    · rename_i hX hY
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨_, List.mem_of_getElem? hX, _, List.mem_of_getElem? hY, h.1.1, h.1.2, h.2⟩
    · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- A final factorization: every even permutation fixing the placed points is a product of an `X` and a `Y`. -/
theorem xFinalOK_sound {main : ExactEntry → Fin 24 → Fin 24} {G F P : List (Fin 24)}
    {lX lY : ExactLevel} {tab : List (List (Fin 24) × ℕ × ℕ)}
    (h : xFinalOK main G F P lX lY tab = true) (E : ExactEntry → Perm (Fin 24))
    (hE : ∀ ε, xEntryOK F P ε = true → (∀ x, E ε x = main ε x) ∧ (∀ g ∈ G, E ε g = g))
    (hsE : ∀ ε, Perm.sign (E ε) = 1) {π : Perm (Fin 24)} (hs : Perm.sign π = 1)
    (hf : ∀ g ∈ G, π g = g) :
    ∃ X ∈ lX.entries, ∃ Y ∈ lY.entries, xEntryOK F P X = true ∧ xEntryOK F P Y = true ∧
      π = E X * E Y := by
  simp only [xFinalOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hX, hY⟩, hrest⟩ := h
  split at hrest
  · rename_i p0 p1 p2 a b hom
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
      List.mem_finRange, true_implies, Bool.or_eq_true] at hrest
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hab, h01⟩, h02⟩, h12⟩, hp0⟩, hp1⟩, hp2⟩, hcov⟩, htab⟩ := hrest
    have nm : ∀ q : Fin 24, G.contains q = false → q ∉ G := fun q hc hm => by
      rw [List.contains_iff_mem.2 hm] at hc
      exact absurd hc (by decide)
    have hin : ∀ q : Fin 24, q ∉ G → π q ∈ lX.omega := fun q hq => by
      rcases hcov (π q) with hc | hc
      · exact absurd (List.contains_iff_mem.1 hc) (image_not_mem hf hq)
      · exact List.contains_iff_mem.1 hc
    have ht := htab _ (hin _ (nm _ hp0)) _ (hin _ (nm _ hp1)) _ (hin _ (nm _ hp2))
    have i : ∀ {u v : Fin 24}, u ≠ v → π u ≠ π v := fun huv => π.injective.ne huv
    have ht' : xWitnessOK main lX lY tab p0 p1 p2 (π p0) (π p1) (π p2) = true := by
      simpa only [i h01, i h02, i h12, false_or] using ht
    obtain ⟨X, hXm, Y, hYm, e0, e1, e2⟩ := xWitnessOK_sound ht'
    refine ⟨X, hXm, Y, hYm, hX X hXm, hY Y hYm, ?_⟩
    obtain ⟨hXa, hXf⟩ := hE X (hX X hXm)
    obtain ⟨hYa, hYf⟩ := hE Y (hY Y hYm)
    have back : ∀ q, main X (main Y q) = π q → ((E Y)⁻¹ * ((E X)⁻¹ * π)) q = q := by
      intro q hq
      rw [Perm.mul_apply, Perm.mul_apply, ← hq, ← hYa, ← hXa]
      simp
    have hρ : (E Y)⁻¹ * ((E X)⁻¹ * π) = 1 := by
      apply even_of_two (p0 :: p1 :: p2 :: G) a b hab
      · intro x
        rcases hcov x with hc | hc
        · exact Or.inl (by simp [List.contains_iff_mem.1 hc])
        · have := List.contains_iff_mem.1 hc
          rw [hom] at this
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          simp only [List.mem_cons]
          tauto
      · simp [hs, hsE]
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact back _ e0
        rcases List.mem_cons.1 hq with rfl | hq
        · exact back _ e1
        rcases List.mem_cons.1 hq with rfl | hq
        · exact back _ e2
        rw [Perm.mul_apply, Perm.mul_apply, hf q hq, Perm.inv_eq_iff_eq.2 (hXf q hq).symm,
          Perm.inv_eq_iff_eq.2 (hYf q hq).symm]
    calc π = E X * (E Y * ((E Y)⁻¹ * ((E X)⁻¹ * π))) := by group
      _ = E X * E Y := by rw [hρ, _root_.mul_one]
  · exact absurd hrest (by decide)

theorem XInv.update {F P : List (Fin 24)} {π₁ π₂ : Perm (Fin 24)} (h : XInv F P π₁ π₂) (τ : Tmpl)
    (h₁ : ∀ f ∈ F, eT τ f = f) (h₂ : ∀ p ∈ P, eM τ p = p) :
    XInv F P ((eT τ)⁻¹ * π₁) ((eM τ)⁻¹ * π₂) where
  s₁ := by simp [h.s₁, sign_eT]
  s₂ := by simp [h.s₂, sign_eM]
  f₁ f hf := by rw [Perm.mul_apply, h.f₁ f hf, Perm.inv_eq_iff_eq.2 (h₁ f hf).symm]
  f₂ p hp := by rw [Perm.mul_apply, h.f₂ p hp, Perm.inv_eq_iff_eq.2 (h₂ p hp).symm]

/-- The lists of a sublist of levels. -/
abbrev xLists (ls : List ExactLevel) : List (List Tmpl) :=
  ls.map fun l => l.entries.map ExactEntry.tmpl

/-- Solutions of the remaining levels for a pair of permutations. -/
def XSol (ls : List ExactLevel) (π₁ π₂ : Perm (Fin 24)) : Prop :=
  ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch (xLists ls) ∧ (ch.map eT).prod = π₁ ∧
    (ch.map eM).prod = π₂

theorem XSol.cons {ls : List ExactLevel} {π₁ π₂ : Perm (Fin 24)} {l : ExactLevel} {ε : ExactEntry}
    (hε : ε ∈ l.entries) (h : XSol ls ((eT ε.tmpl)⁻¹ * π₁) ((eM ε.tmpl)⁻¹ * π₂)) :
    XSol (l :: ls) π₁ π₂ := by
  obtain ⟨ch, h1, h2, h3⟩ := h
  refine ⟨ε.tmpl :: ch, List.Forall₂.cons (List.mem_map_of_mem hε) h1, ?_, ?_⟩
  · simp [h2]
  · simp [h3]

/-- **Soundness of the check.** -/
theorem xChainOK_sound : ∀ (ls : List ExactLevel) (F P : List (Fin 24)),
    xChainOK F P ls = true → ∀ π₁ π₂ : Perm (Fin 24), XInv F P π₁ π₂ → XSol ls π₁ π₂
  | [], F, P, h, π₁, π₂, hI => by
    simp only [xChainOK, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
      List.contains_iff_mem] at h
    refine ⟨[], List.Forall₂.nil, ?_, ?_⟩
    · ext x
      simp [hI.f₁ x (h x).1]
    · ext x
      simp [hI.f₂ x (h x).2]
  | [_], F, P, h, π₁, π₂, hI => by
    simp [xChainOK] at h
  | l :: l₂ :: ls, F, P, h, π₁, π₂, hI => by
    rw [xChainOK] at h
    split at h
    · rename_i b _ _
      simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      obtain ⟨hb, ε, hε, hOK, he⟩ := xLevelOK_sound hl hI.f₁
      obtain ⟨a1, _, a3, a4⟩ := xEntryOK_sound hOK
      have hU := hI.update ε.tmpl a3 a4
      refine XSol.cons hε (xChainOK_sound (l₂ :: ls) (b :: F) P hr _ _ ⟨hU.s₁, hU.s₂, ?_, hU.f₂⟩)
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, a1, he]
      · exact hU.f₁ f hf
    · rename_i b _ _
      simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      obtain ⟨hb, ε, hε, hOK, he⟩ := xLevelOK_sound hl hI.f₂
      obtain ⟨_, a2, a3, a4⟩ := xEntryOK_sound hOK
      have hU := hI.update ε.tmpl a3 a4
      refine XSol.cons hε (xChainOK_sound (l₂ :: ls) F (b :: P) hr _ _ ⟨hU.s₁, hU.s₂, hU.f₁, ?_⟩)
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [Perm.mul_apply, Perm.inv_eq_iff_eq, a2, he]
      · exact hU.f₂ f hf
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      obtain ⟨X, hX, Y, hY, oX, oY, hπ⟩ := xFinalOK_sound hl (fun ε => eT ε.tmpl)
        (fun ε hε => ⟨(xEntryOK_sound hε).1, (xEntryOK_sound hε).2.2.1⟩) (fun ε => sign_eT _)
        hI.s₁ hI.f₁
      obtain ⟨_, _, a3, a4⟩ := xEntryOK_sound oX
      obtain ⟨_, _, b3, b4⟩ := xEntryOK_sound oY
      have hU := (hI.update X.tmpl a3 a4).update Y.tmpl b3 b4
      refine XSol.cons hX (XSol.cons hY
        (xChainOK_sound ls (l.omega ++ F) P hr _ _ ⟨hU.s₁, hU.s₂, ?_, hU.f₂⟩))
      have : (eT Y.tmpl)⁻¹ * ((eT X.tmpl)⁻¹ * π₁) = 1 := by
        rw [hπ]; group
      rw [this]
      simp
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hr⟩ := h
      obtain ⟨X, hX, Y, hY, oX, oY, hπ⟩ := xFinalOK_sound hl (fun ε => eM ε.tmpl)
        (fun ε hε => ⟨(xEntryOK_sound hε).2.1, (xEntryOK_sound hε).2.2.2⟩) (fun ε => sign_eM _)
        hI.s₂ hI.f₂
      obtain ⟨_, _, a3, a4⟩ := xEntryOK_sound oX
      obtain ⟨_, _, b3, b4⟩ := xEntryOK_sound oY
      have hU := (hI.update X.tmpl a3 a4).update Y.tmpl b3 b4
      refine XSol.cons hX (XSol.cons hY
        (xChainOK_sound ls F (l.omega ++ P) hr _ _ ⟨hU.s₁, hU.s₂, hU.f₁, ?_⟩))
      have : (eM Y.tmpl)⁻¹ * ((eM X.tmpl)⁻¹ * π₂) = 1 := by
        rw [hπ]; group
      rw [this]
      simp
    · exact absurd h (by decide)

/-- **The exact lists are universal.** For all even `π₁ π₂`, one template per list has `∏ eT = π₁` and `∏ eM = π₂`. -/
theorem exact_universal : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
    ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch exactLists ∧ (ch.map eT).prod = π₁ ∧
      (ch.map eM).prod = π₂ := fun π₁ π₂ h₁ h₂ =>
  xChainOK_sound exactLevels [] [] exactChain_ok π₁ π₂ ⟨h₁, h₂, by simp, by simp⟩

/-- The sizes of the exact lists. -/
theorem exactLists_sizes : exactLists.map List.length = [24, 24, 23, 23, 22, 22, 21, 21, 20, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 12, 5, 12] := by
  decide +kernel

/-- **The product of the sizes** is `(24!/2)²`, the number of pairs of even permutations. -/
theorem exactLists_prod : (exactLists.map List.length).prod = (Nat.factorial 24 / 2) ^ 2 := by
  rw [exactLists_sizes]
  decide +kernel

/-- The longest template of the exact lists has `8` moves. -/
theorem exactLists_tmplLen : ∀ l ∈ exactLists, ∀ t ∈ l, tmplLen t ≤ 8 := by
  decide +kernel

end RubiksGN
