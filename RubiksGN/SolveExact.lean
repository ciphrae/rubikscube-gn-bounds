import RubiksGN.Program
import RubiksGN.Bounds

/-!
# Solving every position with the round scheme

The `r = n / 2 - 1` rows are cut in consecutive coarse blocks of `S` rows. A pair of indices in different
blocks is handled once, by the program of the earlier block: both its orbits are solved at once. All other
orbits, those of two indices in one block and those of the outer and the middle column, are acted on by `1`
by every program, and they are finished by the old gadget on singletons.
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-! ### Parity and skeleton -/

/-- The parity repair and the skeleton step. -/
theorem exists_prep (hn : 3 ≤ n) (w₀ : Word n) (hw₀ : ∀ m ∈ w₀, IsQ m) :
    ∃ (Wp a₁ : Word n), a₁ = Wp ++ w₀ ∧ (∀ m ∈ Wp, IsQ m) ∧ (∀ m ∈ a₁, IsQ m) ∧
      Wp.length ≤ 3 * n + 406 ∧ EvenW a₁ ∧
      (∀ k, Word.eval a₁ (e (rep (row0 hn) (layerOf hn 2)) k) =
        e (rep (row0 hn) (layerOf hn 2)) k) ∧
      (∀ j : Fin n, layerZ n j = 0 → ∀ k, Word.eval a₁ (e (rep (row0 hn) j) k) =
        e (rep (row0 hn) j) k) ∧
      (∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval a₁ (e (rep m m) k) = e (rep m m) k) := by
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
  obtain ⟨Ws, hsQ, hslen, hsE, hC, hE, hZ⟩ := skel_word hn a haQ ha
  refine ⟨Ws ++ Word.inv u, Ws ++ a, by simp [a], ?_, ?_, ?_, hsE.append ha, ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hsQ m h
    · exact Word.inv_isQ u huQ m h
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hsQ m h
    · exact haQ m h
  · simp only [List.length_append, Word.inv_length]
    omega
  · intro k
    simp only [Word.eval_append, Perm.mul_apply]
    exact hC k
  · intro j hj k
    simp only [Word.eval_append, Perm.mul_apply]
    exact hE j hj k
  · intro m hm k
    simp only [Word.eval_append, Perm.mul_apply]
    exact hZ m hm k

/-- A word fixing all orbits of rows and columns and the skeleton is the identity. -/
theorem eval_eq_one_of_orbits (hn : 3 ≤ n) (W : Word n) (hWQ : ∀ m ∈ W, IsQ m)
    (hrow : ∀ i j : Fin n, IsRow i → IsCol j → ∀ k,
      Word.eval W (e (rep i j) k) = e (rep i j) k)
    (hskel1 : ∀ k, Word.eval W (e (rep (row0 hn) (layerOf hn 2)) k) =
      e (rep (row0 hn) (layerOf hn 2)) k)
    (hskel2 : ∀ j : Fin n, layerZ n j = 0 → ∀ k, Word.eval W (e (rep (row0 hn) j) k) =
      e (rep (row0 hn) j) k)
    (hskel3 : ∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval W (e (rep m m) k) = e (rep m m) k) :
    Word.eval W = 1 := by
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

/-! ### The old gadget on single orbits -/

/-- A list of letters on one orbit, and the identity on every other orbit. -/
theorem exists_single (hn : 2 ≤ n) {i j : Fin n} (hi : IsRow i) (hj : IsCol j) (T : List Letter) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length = 8 * T.length ∧ FixesSkel hn w ∧
      (∀ k, Word.eval w (e (rep i j) k) = e (rep i j) (prodL T k)) ∧
      (∀ i' j' : Fin n, IsRow i' → IsCol j' → (i', j') ≠ (i, j) → ∀ k,
        Word.eval w (e (rep i' j') k) = e (rep i' j') k) := by
  have hX : ∀ x ∈ ({i} : Finset (Fin n)), IsRow x := fun x hx => by
    rw [Finset.mem_singleton.1 hx]; exact hi
  have hY : ∀ x ∈ ({j} : Finset (Fin n)), IsCol x := fun x hx => by
    rw [Finset.mem_singleton.1 hx]; exact hj
  induction T with
  | nil => exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp [prodL], by simp⟩
  | cons l t ih =>
    obtain ⟨w, h1, h2, h3, h4, h5⟩ := ih
    refine ⟨gadgetW hn l {i} {j} ++ w, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact gadgetW_isQ _ _ _ _ _ h
      · exact h1 m h
    · simp only [List.length_append, gadgetW_length, Finset.card_singleton, h2, List.length_cons]
      ring
    · exact (gadget_fixesSkel hn l _ _ hX hY).append h3
    · intro k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [h4, gadget_on hn l _ _ hX hY i j (by simp) (by simp)]
      simp [prodL]
    · intro i' j' hi' hj' hne k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [h5 i' j' hi' hj' hne]
      apply gadget_off hn l _ _ hX hY i' j' (row_col_dom i' j' hi' hj')
      · simp only [Finset.mem_singleton]
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      · rintro ⟨h0, _⟩
        simp only [IsRow] at hi'
        omega

/-- The cleanup: on each orbit of a list, its own list of letters from the universal sequence. -/
theorem exists_cleanup (hn : 2 ≤ n) (T : Fin n → Fin n → List Letter)
    (hT : ∀ i j, (T i j).Sublist uSeq) :
    ∀ B : List (Fin n × Fin n), B.Nodup → (∀ p ∈ B, IsRow p.1 ∧ IsCol p.2) →
      ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ 2200 * B.length ∧ FixesSkel hn w ∧
        ∀ i j : Fin n, IsRow i → IsCol j → ∀ k,
          ((i, j) ∈ B → Word.eval w (e (rep i j) k) = e (rep i j) (prodL (T i j) k)) ∧
          ((i, j) ∉ B → Word.eval w (e (rep i j) k) = e (rep i j) k) := by
  intro B
  induction B with
  | nil =>
    intro _ _
    exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp⟩
  | cons p t ih =>
    intro hnd hB
    obtain ⟨hpt, htn⟩ := List.nodup_cons.1 hnd
    obtain ⟨w, h1, h2, h3, h4⟩ := ih htn (fun x hx => hB x (List.mem_cons_of_mem _ hx))
    obtain ⟨hpi, hpj⟩ := hB p List.mem_cons_self
    obtain ⟨w', g1, g2, g3, g4, g5⟩ := exists_single hn hpi hpj (T p.1 p.2)
    refine ⟨w' ++ w, ?_, ?_, g3.append h3, ?_⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact g1 m h
      · exact h1 m h
    · have hlen : (T p.1 p.2).length ≤ 275 := by
        have := (hT p.1 p.2).length_le
        rwa [uSeq_length] at this
      simp only [List.length_append, List.length_cons, g2]
      omega
    · intro i j hi hj k
      simp only [Word.eval_append, Perm.mul_apply]
      obtain ⟨A1, A2⟩ := h4 i j hi hj k
      constructor
      · intro hmem
        by_cases hij : (i, j) = p
        · subst hij
          rw [A2 hpt]
          exact g4 k
        · have hmt : (i, j) ∈ t := (List.mem_cons.1 hmem).resolve_left hij
          rw [A1 hmt]
          exact g5 i j hi hj hij _
      · intro hmem
        have hij : (i, j) ≠ p := fun h => hmem (h ▸ List.mem_cons_self)
        have hmt : (i, j) ∉ t := fun h => hmem (List.mem_cons_of_mem _ h)
        rw [A2 hmt]
        exact g5 i j hi hj hij _

/-! ### The coarse blocks -/

/-- A coarse block of rows. -/
def blockQ (n S t : ℕ) : Finset (Fin n) := (rowsF n).filter fun i => (i.val - 1) / S = t

/-- The columns of the later blocks. -/
def blockY (n S t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.rev j ∈ rowsF n ∧ t < ((Fin.rev j).val - 1) / S

theorem mem_rowsF {i : Fin n} : i ∈ rowsF n ↔ IsRow i := by
  simp [rowsF, IsRow]

theorem mem_colsF {j : Fin n} : j ∈ colsF n ↔ IsCol j := by
  simp [colsF, IsCol]

theorem mem_blockQ {S t : ℕ} {i : Fin n} :
    i ∈ blockQ n S t ↔ IsRow i ∧ (i.val - 1) / S = t := by
  simp [blockQ, mem_rowsF]

theorem mem_blockY {S t : ℕ} {j : Fin n} :
    j ∈ blockY n S t ↔ IsRow (Fin.rev j) ∧ t < ((Fin.rev j).val - 1) / S := by
  simp [blockY, mem_rowsF]

theorem block_ctx (S t : ℕ) : PairCtx (blockQ n S t) (blockY n S t) where
  hX := fun i hi => (mem_blockQ.1 hi).1
  hY := fun j hj => by
    have h := isRow_coord (mem_blockY.1 hj).1
    rw [layerZ_rev] at h
    omega
  hXY := fun i hi j hj he => by
    have hji : j = Fin.rev i := layerZ_inj _ _ (by rw [layerZ_rev]; exact he)
    subst hji
    have h1 := (mem_blockY.1 hj).2
    rw [Fin.rev_rev, (mem_blockQ.1 hi).2] at h1
    exact lt_irrefl _ h1

theorem card_blockQ_le (S t : ℕ) (hS : 0 < S) : (blockQ n S t).card ≤ S := by
  have h : (blockQ n S t).card ≤ (Finset.Ico (S * t) (S * t + S)).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.val - 1)
    · intro i hi
      have h1 := (mem_blockQ.1 hi).2
      have h2 := Nat.div_add_mod (i.val - 1) S
      have h3 := Nat.mod_lt (i.val - 1) hS
      rw [h1] at h2
      simp only [Finset.coe_Ico, Set.mem_Ico]
      omega
    · intro x hx y hy hxy
      have hx1 := (mem_blockQ.1 hx).1.1
      have hy1 := (mem_blockQ.1 hy).1.1
      simp only at hxy
      apply Fin.ext
      omega
  simpa using h

theorem card_blockY_le (S t : ℕ) (hS : 0 < S) :
    (blockY n S t).card ≤ (n / 2 - 1) - (t + 1) * S := by
  have h : (blockY n S t).card ≤ (Finset.Ico ((t + 1) * S) (n / 2 - 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (Fin.rev j).val - 1)
    · intro j hj
      obtain ⟨h1, h2⟩ := mem_blockY.1 hj
      simp only [IsRow] at h1
      have h3 : (t + 1) * S ≤ (Fin.rev j).val - 1 := (Nat.le_div_iff_mul_le hS).1 h2
      simp only [Finset.coe_Ico, Set.mem_Ico]
      omega
    · intro x hx y hy hxy
      have hx1 := (mem_blockY.1 hx).1.1
      have hy1 := (mem_blockY.1 hy).1.1
      simp only at hxy
      apply Fin.rev_injective
      apply Fin.ext
      omega
  simpa using h

/-- `S * Σ_t 2 y_t ≤ r²`, where `y_t = r - (t + 1) S`. -/
theorem sum_blocks_mul_le (S : ℕ) (hS : 0 < S) (r : ℕ) :
    (∑ t ∈ Finset.range (r / S + 1), 2 * (r - (t + 1) * S)) * S ≤ r ^ 2 := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases h : r < S
    · have h0 : r / S = 0 := Nat.div_eq_of_lt h
      rw [h0]
      have : r - (0 + 1) * S = 0 := by rw [zero_add, one_mul]; omega
      rw [zero_add, Finset.sum_range_one, this]
      simp
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
      have ihq := ih q (by omega)
      rw [Nat.add_div_left _ hS, Finset.sum_range_succ']
      have hterm : ∀ t, 2 * (S + q - (t + 1 + 1) * S) = 2 * (q - (t + 1) * S) := by
        intro t
        have : (t + 1 + 1) * S = (t + 1) * S + S := by ring
        rw [this]
        omega
      simp only [hterm]
      have h0 : 2 * (S + q - (0 + 1) * S) = 2 * q := by
        rw [zero_add, one_mul]
        omega
      rw [h0]
      nlinarith

/-- **The sum bound.** The columns of all programs take at most `r² / S` moves per round. -/
theorem sum_blocks_le (S : ℕ) (hS : 0 < S) (r : ℕ) :
    ∑ t ∈ Finset.range (r / S + 1), 2 * (r - (t + 1) * S) ≤ r ^ 2 / S :=
  (Nat.le_div_iff_mul_le hS).2 (sum_blocks_mul_le S hS r)

/-! ### Which block handles an orbit -/

/-- The block `t` handles the orbit of `(i, j)`. -/
def Handled (n S t : ℕ) (i j : Fin n) : Prop :=
  (i ∈ blockQ n S t ∧ j ∈ blockY n S t) ∨
    (Fin.rev j ∈ blockQ n S t ∧ Fin.rev i ∈ blockY n S t)

theorem handled_iff {S t : ℕ} {i j : Fin n} (hi : IsRow i) :
    Handled n S t i j ↔ IsRow (Fin.rev j) ∧
      (((i.val - 1) / S = t ∧ t < ((Fin.rev j).val - 1) / S) ∨
        (((Fin.rev j).val - 1) / S = t ∧ t < (i.val - 1) / S)) := by
  simp only [Handled, mem_blockQ, mem_blockY, Fin.rev_rev]
  tauto

theorem handled_unique {S t t' : ℕ} {i j : Fin n} (hi : IsRow i) (h : Handled n S t i j)
    (h' : Handled n S t' i j) : t = t' := by
  obtain ⟨_, h1⟩ := (handled_iff hi).1 h
  obtain ⟨_, h2⟩ := (handled_iff hi).1 h'
  omega

theorem row_val_le {i : Fin n} (hi : IsRow i) : i.val - 1 ≤ n / 2 - 1 := by
  simp only [IsRow] at hi
  omega

/-- An orbit is handled exactly when it joins two different blocks. -/
theorem exists_handled_iff {S : ℕ} {i j : Fin n} (hi : IsRow i) :
    (∃ t, t < (n / 2 - 1) / S + 1 ∧ Handled n S t i j) ↔
      Fin.rev j ∈ rowsF n ∧ (i.val - 1) / S ≠ ((Fin.rev j).val - 1) / S := by
  constructor
  · rintro ⟨t, _, h⟩
    obtain ⟨h1, h2⟩ := (handled_iff hi).1 h
    exact ⟨mem_rowsF.2 h1, by omega⟩
  · rintro ⟨h1, h2⟩
    have hr := mem_rowsF.1 h1
    have ha : (i.val - 1) / S ≤ (n / 2 - 1) / S := Nat.div_le_div_right (row_val_le hi)
    have hb : ((Fin.rev j).val - 1) / S ≤ (n / 2 - 1) / S := Nat.div_le_div_right (row_val_le hr)
    rcases Nat.lt_or_gt_of_ne h2 with h3 | h3
    · exact ⟨(i.val - 1) / S, by omega, (handled_iff hi).2 ⟨hr, Or.inl ⟨rfl, h3⟩⟩⟩
    · exact ⟨((Fin.rev j).val - 1) / S, by omega, (handled_iff hi).2 ⟨hr, Or.inr ⟨rfl, h3⟩⟩⟩

/-! ### The orbits left to the gadget -/

/-- The orbits that no program handles. -/
def badOrbits (n S : ℕ) : Finset (Fin n × Fin n) :=
  (rowsF n ×ˢ colsF n).filter fun p =>
    ¬ (Fin.rev p.2 ∈ rowsF n ∧ (p.1.val - 1) / S ≠ ((Fin.rev p.2).val - 1) / S)

theorem mem_badOrbits {S : ℕ} {i j : Fin n} :
    (i, j) ∈ badOrbits n S ↔ IsRow i ∧ IsCol j ∧
      ¬ (Fin.rev j ∈ rowsF n ∧ (i.val - 1) / S ≠ ((Fin.rev j).val - 1) / S) := by
  simp only [badOrbits, Finset.mem_filter, Finset.mem_product, mem_rowsF, mem_colsF, and_assoc]

/-- At most `r (S + 2)` orbits are left to the gadget. -/
theorem card_badOrbits_le (hn : 2 ≤ n) (S : ℕ) (hS : 0 < S) :
    (badOrbits n S).card ≤ (n / 2 - 1) * (S + 2) := by
  have hfib : ∀ a ∈ (badOrbits n S).image Prod.fst,
      ((badOrbits n S).filter fun x => x.1 = a).card ≤ S + 2 := by
    intro a _
    let C : Finset (Fin n) := ({⟨n - 1, by omega⟩, ⟨(n - 1) / 2, by omega⟩} : Finset (Fin n)) ∪
      (blockQ n S ((a.val - 1) / S)).image Fin.rev
    have hC : C.card ≤ S + 2 := by
      have h1 : (({⟨n - 1, by omega⟩, ⟨(n - 1) / 2, by omega⟩} : Finset (Fin n))).card ≤ 2 :=
        Finset.card_le_two
      have h2 := (Finset.card_image_le (s := blockQ n S ((a.val - 1) / S)) (f := Fin.rev)).trans
        (card_blockQ_le S _ hS)
      have h3 := Finset.card_union_le ({⟨n - 1, by omega⟩, ⟨(n - 1) / 2, by omega⟩} : Finset (Fin n))
        ((blockQ n S ((a.val - 1) / S)).image Fin.rev)
      simp only [C]
      omega
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) hC
    · rintro ⟨x, j⟩ hx
      have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      obtain ⟨h1, rfl⟩ := hx'
      obtain ⟨hr, hc, hb⟩ := mem_badOrbits.1 h1
      simp only [C, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton, Finset.coe_image,
        Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Finset.mem_coe]
      by_cases hrj : Fin.rev j ∈ rowsF n
      · right
        refine ⟨Fin.rev j, mem_blockQ.2 ⟨mem_rowsF.1 hrj, ?_⟩, Fin.rev_rev j⟩
        by_contra hne
        exact hb ⟨hrj, fun h => hne h.symm⟩
      · left
        have hj := j.isLt
        rw [mem_rowsF] at hrj
        simp only [IsRow, Fin.val_rev, not_and, not_lt] at hrj
        simp only [IsCol] at hc
        by_cases h0 : 0 < n - (j.val + 1)
        · right
          have := hrj h0
          apply Fin.ext
          simp only
          omega
        · left
          apply Fin.ext
          simp only
          omega
    · rintro ⟨x, j⟩ hx ⟨x', j'⟩ hx' hjj
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hx')).2
      simp only at h1 h2 hjj
      rw [h1, h2, hjj]
  have himg : ((badOrbits n S).image Prod.fst).card ≤ n / 2 - 1 := by
    rw [← card_rowsF (n := n)]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨⟨x, j⟩, hx, rfl⟩ := Finset.mem_image.1 hi
    exact mem_rowsF.2 (mem_badOrbits.1 hx).1
  calc (badOrbits n S).card ≤ (S + 2) * ((badOrbits n S).image Prod.fst).card :=
        Finset.card_le_mul_card_image _ _ hfib
    _ ≤ (S + 2) * (n / 2 - 1) := Nat.mul_le_mul_left _ himg
    _ = _ := by ring

/-! ### All programs -/

/-- The programs of the first `m` blocks. -/
theorem exists_programs (hn : 2 ≤ n) (ls : List (List Tmpl)) (hne : ∀ l ∈ ls, l ≠ []) (L : ℕ)
    (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L) (sOf : ℕ → ℕ)
    (hs : ∀ m ∈ ls.map List.length, 0 < sOf m) (Cslot : ℕ)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) (S : ℕ) (hS0 : 0 < S)
    (hS : Even S)
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (π : Fin n → Fin n → Perm (Fin 24)) (hπ : ∀ i j, Perm.sign (π i j) = 1) (m : ℕ) :
    ∃ P : Word n, (∀ m ∈ P, IsQ m) ∧
      P.length ≤ exactRounds S sOf (ls.map List.length) *
        (∑ t ∈ Finset.range m, (2 * (blockY n S t).card + 2 * Cslot)) ∧
      FixesSkel hn P ∧ ∀ i j, IsRow i → IsCol j →
        ((∃ t, t < m ∧ Handled n S t i j) → Rv (rep i j) P = π i j) ∧
        ((¬ ∃ t, t < m ∧ Handled n S t i j) → Rv (rep i j) P = 1) := by
  classical
  induction m with
  | zero => exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp⟩
  | succ m ih =>
    obtain ⟨P, p1, p2, p3, p4⟩ := ih
    obtain ⟨W, w1, w2, w3, w4⟩ := program_solve hn ls hne L hL sOf hs Cslot hC S hS huniv
      (block_ctx (n := n) S m) (card_blockQ_le S m hS0) π hπ
    refine ⟨P ++ W, ?_, ?_, p3.append w3, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact p1 x h
      · exact w1 x h
    · rw [Finset.sum_range_succ, Nat.mul_add, List.length_append]
      omega
    · intro i j hi hj
      obtain ⟨A1, A2⟩ := p4 i j hi hj
      have hW := w4 i j hi hj
      rw [Rv_append, hW]
      by_cases hH : Handled n S m i j
      · have hno : ¬ ∃ t, t < m ∧ Handled n S t i j := by
          rintro ⟨t, ht, h⟩
          have := handled_unique hi h hH
          omega
        have hH' : (i ∈ blockQ n S m ∧ j ∈ blockY n S m) ∨
            (Fin.rev j ∈ blockQ n S m ∧ Fin.rev i ∈ blockY n S m) := hH
        rw [if_pos hH', A2 hno, one_mul]
        exact ⟨fun _ => rfl, fun h => absurd ⟨m, by omega, hH⟩ h⟩
      · have hH' : ¬ ((i ∈ blockQ n S m ∧ j ∈ blockY n S m) ∨
            (Fin.rev j ∈ blockQ n S m ∧ Fin.rev i ∈ blockY n S m)) := hH
        rw [if_neg hH', mul_one]
        constructor
        · rintro ⟨t, ht, h⟩
          apply A1
          refine ⟨t, ?_, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | rfl
          · exact h'
          · exact absurd h hH
        · intro h
          exact A2 fun ⟨t, ht, h'⟩ => h ⟨t, by omega, h'⟩

/-! ### The theorem -/

theorem forall₂_right_nonempty {α β : Type*} {R : α → β → Prop} {ch : List α} {ls : List β}
    (h : List.Forall₂ R ch ls) : ∀ l ∈ ls, ∃ a, R a l := by
  induction h with
  | nil => simp
  | cons h1 _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ⟨_, h1⟩
    · exact ih l hl

/-- **Every position is solved in `exactW` quarter turns**, given universal lists. -/
theorem solve_exact (hn : 3 ≤ n) (ls : List (List Tmpl))
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (S : ℕ) (hS0 : 0 < S) (hS : Even S) (sOf : ℕ → ℕ) (hs : ∀ m ∈ ls.map List.length, 0 < sOf m)
    (L Cslot : ℕ) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot)
    (g : Perm (Sticker n)) (hg : g ∈ cubeGroup n) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ exactW n S Cslot sOf (ls.map List.length) ∧
      Word.eval w * g = 1 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hne : ∀ l ∈ ls, l ≠ [] := by
    intro l hl he
    obtain ⟨ch, h1, _⟩ := huniv 1 1 (by simp) (by simp)
    obtain ⟨a, ha⟩ := forall₂_right_nonempty h1 l hl
    simp [he] at ha
  obtain ⟨w₀, hw₀, rfl⟩ := word_of_mem g hg
  obtain ⟨Wp, a₁, ha₁, hpQ, ha₁Q, hplen, ha₁E, hskC, hskE, hskZ⟩ := exists_prep hn w₀ hw₀
  let π : Fin n → Fin n → Perm (Fin 24) := fun i j => (Rv (rep i j) a₁)⁻¹
  have hπ : ∀ i j, Perm.sign (π i j) = 1 := fun i j => by
    simp only [π]
    rw [Perm.sign_inv]
    exact sign_Rv _ _ ha₁E
  obtain ⟨P, p1, p2, p3, p4⟩ := exists_programs hn2 ls hne L hL sOf hs Cslot hC S hS0 hS huniv π hπ
    ((n / 2 - 1) / S + 1)
  have hun := fun i j => universal (π i j) (hπ i j)
  choose T hT1 hT2 using hun
  obtain ⟨Wb, b1, b2, b3, b4⟩ := exists_cleanup hn2 T hT1 (badOrbits n S).toList
    (Finset.nodup_toList _) (fun p hp => by
      obtain ⟨x, y⟩ := p
      have := mem_badOrbits.1 (Finset.mem_toList.1 hp)
      exact ⟨this.1, this.2.1⟩)
  rw [Finset.length_toList] at b2
  have hcard := card_badOrbits_le hn2 S hS0
  -- the length of the programs
  have hsum : (∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), (2 * (blockY n S t).card + 2 * Cslot)) ≤
      (n / 2 - 1) ^ 2 / S + 2 * ((n / 2 - 1) / S + 1) * Cslot := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h1 : ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * (blockY n S t).card ≤
        ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * ((n / 2 - 1) - (t + 1) * S) :=
      Finset.sum_le_sum fun t _ => Nat.mul_le_mul_left _ (card_blockY_le S t hS0)
    have h2 := sum_blocks_le S hS0 (n / 2 - 1)
    have h3 : ((n / 2 - 1) / S + 1) * (2 * Cslot) = 2 * ((n / 2 - 1) / S + 1) * Cslot := by ring
    omega
  have hPlen : P.length ≤ exactRounds S sOf (ls.map List.length) *
      ((n / 2 - 1) ^ 2 / S + 2 * ((n / 2 - 1) / S + 1) * Cslot) :=
    p2.trans (Nat.mul_le_mul_left _ hsum)
  have hfQ : ∀ m ∈ Wb ++ P, IsQ m := by
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact b1 m h
    · exact p1 m h
  have hfS : FixesSkel hn2 (Wb ++ P) := b3.append p3
  refine ⟨(Wb ++ P) ++ Wp, ?_, ?_, ?_⟩
  · intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact hfQ m h
    · exact hpQ m h
  · simp only [exactW, List.length_append]
    have : 2200 * (badOrbits n S).card ≤ 2200 * ((n / 2 - 1) * (S + 2)) :=
      Nat.mul_le_mul_left _ hcard
    omega
  · have hval : Word.eval ((Wb ++ P) ++ Wp) * Word.eval w₀ = Word.eval ((Wb ++ P) ++ a₁) := by
      rw [ha₁]
      simp only [Word.eval_append, _root_.mul_assoc]
    rw [hval]
    have hWQ : ∀ m ∈ (Wb ++ P) ++ a₁, IsQ m := by
      intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact hfQ m h
      · exact ha₁Q m h
    apply eval_eq_one_of_orbits hn _ hWQ
    · intro i j hi hj k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [word_Rv _ a₁ ha₁Q, word_Rv _ P p1]
      obtain ⟨A1, A2⟩ := p4 i j hi hj
      by_cases hH : ∃ t, t < (n / 2 - 1) / S + 1 ∧ Handled n S t i j
      · have hgood := (exists_handled_iff hi).1 hH
        have hnb : (i, j) ∉ (badOrbits n S).toList := fun h =>
          (mem_badOrbits.1 (Finset.mem_toList.1 h)).2.2 hgood
        rw [A1 hH, (b4 i j hi hj _).2 hnb]
        simp [π]
      · have hbad : (i, j) ∈ (badOrbits n S).toList := Finset.mem_toList.2
          (mem_badOrbits.2 ⟨hi, hj, fun h => hH ((exists_handled_iff hi).2 h)⟩)
        rw [A2 hH, Perm.one_apply, (b4 i j hi hj _).1 hbad, hT2]
        simp [π]
    · intro k
      rw [Word.eval_append, Perm.mul_apply, hskC k]
      exact hfS.1 (layerOf hn 2) (Or.inl rfl) k
    · intro j hj k
      rw [Word.eval_append, Perm.mul_apply, hskE j hj k]
      exact hfS.1 j (Or.inr hj) k
    · intro m hm k
      rw [Word.eval_append, Perm.mul_apply, hskZ m hm k]
      exact hfS.2 m hm k

/-- **Upper bound of the round scheme**, for abstract universal lists. -/
theorem godLabelled_le_exactW (μ : Metric) (hn : 3 ≤ n) (ls : List (List Tmpl))
    (huniv : ∀ π₁ π₂ : Perm (Fin 24), Perm.sign π₁ = 1 → Perm.sign π₂ = 1 →
      ∃ ch : List Tmpl, List.Forall₂ (· ∈ ·) ch ls ∧ (ch.map eT).prod = π₁ ∧ (ch.map eM).prod = π₂)
    (S : ℕ) (hS0 : 0 < S) (hS : Even S) (sOf : ℕ → ℕ) (hs : ∀ m ∈ ls.map List.length, 0 < sOf m)
    (L Cslot : ℕ) (hL : ∀ l ∈ ls, ∀ t ∈ l, tmplLen t ≤ L)
    (hC : ∀ m ∈ ls.map List.length, m ^ sOf m * (2 * sOf m * L) ≤ Cslot) :
    godLabelled μ n ≤ exactW n S Cslot sOf (ls.map List.length) := by
  apply Nat.sInf_le
  intro g hg
  obtain ⟨w, h1, h2, h3⟩ := solve_exact hn ls huniv S hS0 hS sOf hs L Cslot hL hC g hg
  exact ⟨w, fun m hm => allows_of_isQ μ m (h1 m hm), h2, h3⟩

end RubiksGN
