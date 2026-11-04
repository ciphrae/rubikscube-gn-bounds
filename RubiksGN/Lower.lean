import RubiksGN.Solve

/-!
# The counting lower bound

On each of the `(n/2 - 1)(n - n/2 - 1)` inner orbits the colours can be arranged in any of
`Z = 24! / (4!)^6` ways, independently of the other orbits. At most `6^6 (9n+1)^k` positions are
within `k` moves of a position with monochromatic faces.
-/

open Equiv

namespace RubiksGN

open Classical

variable {n : ℕ}

/-- The colour of an orbit coordinate. -/
def kc (k : Fin 24) : Fin 6 := faceAct k 0

/-- The number of arrangements of the colours on one orbit. -/
def Zval : ℕ := Nat.factorial 24 / 24 ^ 6

theorem Zval_eq : Zval = 3246670537110000 := by decide +kernel

theorem Zval_mul : Zval * 24 ^ 6 = Nat.factorial 24 := by decide +kernel

/-- The face of a vector on a cube of half-width `N`. -/
def faceV (N : ℤ) (v : V) : Fin 6 :=
  if v.2.2 = N then 0 else if v.2.2 = -N then 1
  else if v.2.1 = N then 2 else if v.2.1 = -N then 3
  else if v.1 = N then 4 else 5

set_option maxHeartbeats 8000000 in
theorem faceV_act (x y N : ℤ) (hN : 0 < N) (h1 : x ≠ N ∧ x ≠ -N) (h2 : y ≠ N ∧ y ≠ -N) (k : Fin 24) :
    faceV N (act k (x, y, N)) = kc k := by
  obtain ⟨k, hk⟩ := k
  interval_cases k <;> simp only [act, actN, faceV] <;> split_ifs <;> first | rfl | omega

theorem faceOf_e (i j : Fin n) (h1 : layerZ n i ≠ n ∧ layerZ n i ≠ -(n : ℤ))
    (h2 : layerZ n j ≠ n ∧ layerZ n j ≠ -(n : ℤ)) (h0 : 0 < n) (k : Fin 24) :
    faceOf (e (rep i j) k) = kc k :=
  faceV_act _ _ _ (by omega) h1 h2 k

/-! ### The arrangements of the colours on one orbit -/

/-- All arrangements of the colours. -/
@[irreducible] noncomputable def Bal : Finset (Fin 24 → Fin 6) :=
  (Finset.univ : Finset (Perm (Fin 24))).image fun σ => kc ∘ σ

theorem mem_Bal (f : Fin 24 → Fin 6) : f ∈ Bal ↔ ∃ σ : Perm (Fin 24), kc ∘ σ = f := by
  unfold Bal
  simp

theorem kc_fiber : ∀ c : Fin 6, Fintype.card {a : Fin 24 // kc a = c} = 4 := by decide +kernel

/-- The order of the group permuting stickers of equal colour on one orbit. -/
def stabN : ℕ := 24 ^ 6

theorem stabN_mul : Zval * stabN = Nat.factorial 24 := Zval_mul

theorem card_stab : Fintype.card {g : Perm (Fin 24) // kc ∘ g = kc} = stabN := by
  rw [DomMulAct.stabilizer_card]
  simp only [kc_fiber]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem card_fiber (f : Fin 24 → Fin 6) (hf : f ∈ Bal) :
    ((Finset.univ : Finset (Perm (Fin 24))).filter fun σ : Perm (Fin 24) => kc ∘ ⇑σ = f).card = stabN := by
  obtain ⟨σ, rfl⟩ := (mem_Bal f).1 hf
  rw [← card_stab, ← Fintype.card_coe]
  apply Fintype.card_congr
  refine ⟨fun x => ⟨x.1 * σ⁻¹, ?_⟩, fun y => ⟨y.1 * σ, ?_⟩, ?_, ?_⟩
  · have := (Finset.mem_filter.1 x.2).2
    funext a
    have h2 := congrFun this (σ⁻¹ a)
    simpa using h2
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext a
    have h2 := congrFun y.2 (σ a)
    simpa using h2
  · intro x; apply Subtype.ext; simp
  · intro y; apply Subtype.ext; simp

theorem stabN_pos : 0 < stabN := by unfold stabN; positivity

theorem card_perm24 : (Finset.univ : Finset (Perm (Fin 24))).card = Nat.factorial 24 := by
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

theorem card_mul_of_fibers {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (B : Finset β)
    (hmap : ∀ a, f a ∈ B) (c : ℕ) (hc : ∀ b ∈ B, (Finset.univ.filter fun a => f a = b).card = c) :
    B.card * c = (Finset.univ : Finset α).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := B) (fun a _ => hmap a),
    Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]

theorem card_Bal_mul : Bal.card * stabN = (Finset.univ : Finset (Perm (Fin 24))).card :=
  card_mul_of_fibers (fun σ : Perm (Fin 24) => kc ∘ ⇑σ) Bal
    (fun σ => (mem_Bal _).2 ⟨σ, rfl⟩) stabN card_fiber

theorem card_Bal : Bal.card = Zval :=
  Nat.eq_of_mul_eq_mul_right stabN_pos
    (card_Bal_mul.trans (card_perm24.trans stabN_mul.symm))

/-- Two coordinates with the same colour. -/
theorem kc_same : ∃ a b : Fin 24, a ≠ b ∧ kc a = kc b := by decide +kernel

theorem even_of_Bal (f : Fin 24 → Fin 6) (hf : f ∈ Bal) :
    ∃ σ : Perm (Fin 24), Perm.sign σ = 1 ∧ kc ∘ σ = f := by
  obtain ⟨σ, rfl⟩ := (mem_Bal f).1 hf
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact ⟨σ, h, rfl⟩
  · obtain ⟨a, b, hab, hk⟩ := kc_same
    refine ⟨swap a b * σ, by simp [h, Perm.sign_swap hab], ?_⟩
    funext x
    simp only [Function.comp, Perm.mul_apply]
    by_cases h1 : σ x = a
    · rw [h1, swap_apply_left, hk]
    · by_cases h2 : σ x = b
      · rw [h2, swap_apply_right, hk]
      · rw [swap_apply_of_ne_of_ne h1 h2]

/-! ### Rows and columns of the inner orbits -/

/-- The inner columns. -/
def cols'F (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => n ≤ 2 * j.val + 1 ∧ j.val + 1 < n

theorem card_cols'F : (cols'F n).card = n - n / 2 - 1 := by
  have := card_fin_range (n := n) (n / 2) (n - 1) (by omega)
    (fun j => n ≤ 2 * j.val + 1 ∧ j.val + 1 < n) (by intro i; omega)
  simp only [cols'F]
  rw [this]
  omega

/-- The number of independent inner orbits. -/
def innerOrbits (n : ℕ) : ℕ := (n / 2 - 1) * (n - n / 2 - 1)

/-! ### Independent arrangements on all inner orbits -/

/-- The inner orbits, as a type. -/
abbrev Inner (n : ℕ) := {p : Fin n × Fin n // p ∈ rowsF n ×ˢ cols'F n}

theorem card_Inner : Fintype.card (Inner n) = innerOrbits n := by
  rw [Fintype.card_coe, Finset.card_product, card_rowsF, card_cols'F]
  rfl

theorem eval_mem (w : Word n) : Word.eval w ∈ cubeGroup n := by
  induction w with
  | nil => exact one_mem _
  | cons m t ih =>
    rw [Word.eval_cons]
    exact mul_mem (Subgroup.subset_closure ⟨m, rfl⟩) ih

/-- Any choice of arrangements on the inner orbits is realised by an element of the cube group. -/
theorem realise (hn : 3 ≤ n) (F : Inner n → Bal) :
    ∃ g ∈ cubeGroup n, ∀ (p : Inner n) (k : Fin 24),
      colouring g (e (rep p.1.1 p.1.2) k) = (F p).1 k := by
  have hn2 : 2 ≤ n := by omega
  have hR : ∀ i ∈ rowsF n, IsRow i := fun i hi => (Finset.mem_filter.1 hi).2
  have hC : ∀ j ∈ cols'F n, IsCol j := fun j hj => (Finset.mem_filter.1 hj).2.1
  have hσ : ∀ i j : Fin n, ∃ S : List Letter, S.Sublist uSeq ∧
      ∀ hp : (i, j) ∈ rowsF n ×ˢ cols'F n, kc ∘ ⇑((prodL S)⁻¹) = (F ⟨(i, j), hp⟩).1 := by
    intro i j
    by_cases hp : (i, j) ∈ rowsF n ×ˢ cols'F n
    · obtain ⟨σ, h1, h2⟩ := even_of_Bal _ (F ⟨(i, j), hp⟩).2
      obtain ⟨S, hS, hprod⟩ := universal σ⁻¹ (by simpa using h1)
      exact ⟨S, hS, fun _ => by rw [hprod, inv_inv]; exact h2⟩
    · exact ⟨[], List.nil_sublist _, fun h => absurd h hp⟩
  choose S hS1 hS2 using hσ
  obtain ⟨W, _, _, _, hW⟩ := parallel_seq hn2 hR hC 1 one_pos uSeq S (fun i _ j _ => hS1 i j)
  refine ⟨Word.eval W, eval_mem W, ?_⟩
  rintro ⟨⟨i, j⟩, hp⟩ k
  have hp' := Finset.mem_product.1 hp
  have hi := (Finset.mem_filter.1 hp'.1).2
  have hj := (Finset.mem_filter.1 hp'.2).2
  simp only [colouring]
  have hact : (Word.eval W)⁻¹ (e (rep i j) k) = e (rep i j) ((prodL (S i j))⁻¹ k) := by
    rw [Perm.inv_eq_iff_eq, hW i hp'.1 j hp'.2, perm_apply_inv]
  rw [hact, faceOf_e i j]
  · exact congrFun (hS2 i j hp) k
  · have := i.isLt
    simp only [layerZ]
    omega
  · simp only [layerZ]
    omega
  · omega

/-! ### Counting -/

/-- A solved colouring is determined by the colours of the six faces. -/
theorem solved_factor (c : Sticker n → Fin 6) (hc : IsSolved c) :
    ∃ φ : Fin 6 → Fin 6, c = φ ∘ faceOf := by
  refine ⟨fun x => if h : ∃ q, faceOf q = x then c h.choose else 0, ?_⟩
  funext q
  have h : ∃ q', faceOf q' = faceOf q := ⟨q, rfl⟩
  simp only [Function.comp, dif_pos h]
  exact hc _ _ h.choose_spec.symm

theorem colouring_factor (g : Perm (Sticker n)) (w : Word n) (φ : Fin 6 → Fin 6)
    (h : colouring (Word.eval w * g) = φ ∘ faceOf) :
    colouring g = φ ∘ faceOf ∘ Word.eval w := by
  funext q
  have := congrFun h (Word.eval w q)
  simp only [colouring, mul_inv_rev, Perm.mul_apply, perm_inv_apply, Function.comp] at this ⊢
  exact this

/-- Short words, padded to a fixed length. -/
def padW (K : ℕ) (w : Word n) : Fin K → Option (Move n) := fun t => w[t.val]?

theorem padW_inj (K : ℕ) (w w' : Word n) (h1 : w.length ≤ K) (h2 : w'.length ≤ K)
    (h : padW K w = padW K w') : w = w' := by
  apply List.ext_getElem?
  intro t
  by_cases ht : t < K
  · exact congrFun h ⟨t, ht⟩
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem card_move : Fintype.card (Move n) = 9 * n := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  have h1 : Fintype.card Axis = 3 := rfl
  have h2 : Fintype.card Turn = 3 := rfl
  rw [h1, h2]
  ring

/-- **The counting bound.** -/
theorem count_bound (hn : 3 ≤ n) (μ : Metric) (K : ℕ) (hK : ColouredSolvable μ n K) :
    Zval ^ innerOrbits n ≤ 6 ^ 6 * (9 * n + 1) ^ K := by
  choose g hg1 hg2 using realise (n := n) hn
  have hsol : ∀ F : Inner n → Bal, ∃ (φ : Fin 6 → Fin 6) (w : Word n), w.length ≤ K ∧
      colouring (g F) = φ ∘ faceOf ∘ Word.eval w := by
    intro F
    obtain ⟨w, _, hlen, hs⟩ := hK (g F) (hg1 F)
    obtain ⟨φ, hφ⟩ := solved_factor _ hs
    exact ⟨φ, w, hlen, colouring_factor _ _ _ hφ⟩
  choose φ w hlen hfac using hsol
  let Ψ : (Inner n → Bal) → (Fin 6 → Fin 6) × (Fin K → Option (Move n)) :=
    fun F => (φ F, padW K (w F))
  have hinj : Function.Injective Ψ := by
    intro F F' h
    have h1 : φ F = φ F' := congrArg Prod.fst h
    have h2 : w F = w F' := padW_inj K _ _ (hlen F) (hlen F') (congrArg Prod.snd h)
    have hc : colouring (g F) = colouring (g F') := by
      rw [hfac, hfac, h1, h2]
    funext p
    apply Subtype.ext
    funext k
    rw [← hg2 F p k, ← hg2 F' p k, hc]
  have hcard := Fintype.card_le_of_injective Ψ hinj
  have c1 : Fintype.card (Inner n → Bal) = Zval ^ innerOrbits n := by
    rw [Fintype.card_fun, Fintype.card_coe, card_Bal, card_Inner]
  have c2 : Fintype.card ((Fin 6 → Fin 6) × (Fin K → Option (Move n))) =
      6 ^ 6 * (9 * n + 1) ^ K := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_option, card_move]
  rwa [c1, c2] at hcard

end RubiksGN
