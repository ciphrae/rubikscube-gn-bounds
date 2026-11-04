import RubiksGN.ColourChain
import RubiksGN.SolveExact

/-!
# Solving every coloured position

The block structure and the cleanup are those of `SolveExact`. A pair of indices in different blocks is
handled once, by the program of the earlier block, which only has to put the colours right on its two
orbits. The rest (same-block orbits, outer and middle columns, skeleton) is solved exactly.

* `solve_of_chains`: for abstract chains.
* `ColourData`, `ColourData.check`: the finite data and its Boolean check.
* `godColoured_le_colouredW`: **the bound on God's number of the coloured cube.**
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

/-- A family's levels, without parameters. -/
def LevelsOK (L : ℕ) (lv : List CLevel) : Prop :=
  ∀ v ∈ lv, 0 < v.w ∧ v.w ≤ v.l.length ∧ ∀ t ∈ v.l, tmplLen t ≤ L

theorem levelOK_of {L Cslot : ℕ} {sOf Tb : ℕ × ℕ → ℕ} {lv : List CLevel}
    (h : LevelsOK L lv) (hp : ParamsOK n L Cslot sOf Tb (lv.map CLevel.key)) :
    ∀ v ∈ lv, LevelOK L Cslot n sOf Tb v := by
  intro v hv
  have hk : v.key ∈ lv.map CLevel.key := List.mem_map_of_mem hv
  exact ⟨(h v hv).1, (h v hv).2.1, hp.s_pos _ hk, (h v hv).2.2, hp.tb _ hk, hp.slot _ hk⟩

/-- **A program puts the colours right on the two orbits of each pair of a block.** -/
theorem program_col (hn : 2 ≤ n) (lvO lvE : List CLevel) (L Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ)
    (hO : LevelsOK L lvO) (hE : LevelsOK L lvE)
    (hcO : CChain true lvO (fun _ => True) ColGoal) (hcE : CChain false lvE (fun _ => True) ColGoal)
    (ms : List (ℕ × ℕ)) (hmO : lvO.map CLevel.key = ms) (hmE : lvE.map CLevel.key = ms)
    (hp : ParamsOK n L Cslot sOf Tb ms) (S : ℕ) (hS : Even S)
    {Q Y : Finset (Fin n)} (c : PairCtx Q Y) (hQ : Q.card ≤ S) (π : Fin n → Fin n → Perm (Fin 24)) :
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧ W.length ≤ colRounds S sOf ms * (2 * Y.card + 2 * Cslot) ∧
      FixesSkel hn W ∧ ∀ i j, IsRow i → IsCol j →
        (((i ∈ Q ∧ j ∈ Y) ∨ (Fin.rev j ∈ Q ∧ Fin.rev i ∈ Y)) → ColFull (Rv (rep i j) W * π i j)) ∧
        (¬ ((i ∈ Q ∧ j ∈ Y) ∨ (Fin.rev j ∈ Q ∧ Fin.rev i ∈ Y)) → Rv (rep i j) W = 1) := by
  obtain ⟨QO, QE, hU, hd, hcO', hcE'⟩ := exists_split Q S hS hQ
  subst hU
  have hYn : Y.card ≤ n := by
    simpa using Finset.card_le_univ Y
  let s : Fin n → Fin n → CState := fun i j => (π i j, π (Fin.rev j) (Fin.rev i))
  obtain ⟨jsO, o1, o2, o3⟩ := exists_family (R := QO) (Y := Y) true L Cslot n sOf Tb hYn lvO
    (fun _ => True) ColGoal s (levelOK_of hO (hmO ▸ hp)) hcO (fun _ _ _ _ => trivial)
  obtain ⟨jsE, e1, e2, e3⟩ := exists_family (R := QE) (Y := Y) false L Cslot n sOf Tb hYn lvE
    (fun _ => True) ColGoal s (levelOK_of hE (hmE ▸ hp)) hcE (fun _ _ _ _ => trivial)
  have hRO : jsO.length ≤ colRounds S sOf ms := by
    have := family_length_le _ S hcO' sOf lvO
    rw [hmO] at this
    exact o1.trans this
  have hRE : jsE.length ≤ colRounds S sOf ms := by
    have := family_length_le _ S hcE' sOf lvE
    rw [hmE] at this
    exact e1.trans this
  obtain ⟨W, w1, w2, w3, w4⟩ := program_gen hn c hd L Cslot _ jsO jsE hRO hRE o2 e2
  refine ⟨W, w1, w2, w3, ?_⟩
  intro i j hi hj
  have hrr : ∀ x : Fin n, Fin.rev (Fin.rev x) = x := Fin.rev_rev
  rw [w4 i j hi hj]
  constructor
  · intro hH
    by_cases c1 : i ∈ QO ∧ j ∈ Y
    · rw [if_pos c1]
      exact (o3 i c1.1 j c1.2).1
    · rw [if_neg c1]
      by_cases c2 : i ∈ QE ∧ j ∈ Y
      · rw [if_pos c2]
        exact (e3 i c2.1 j c2.2).1
      · rw [if_neg c2]
        by_cases c3 : Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y
        · rw [if_pos c3]
          have := (o3 _ c3.1 _ c3.2).2
          simp only [s, hrr] at this
          exact this
        · rw [if_neg c3]
          have c4 : Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y := by
            rcases hH with ⟨h, hy⟩ | ⟨h, hy⟩
            · rcases Finset.mem_union.1 h with h | h
              · exact absurd ⟨h, hy⟩ c1
              · exact absurd ⟨h, hy⟩ c2
            · rcases Finset.mem_union.1 h with h | h
              · exact absurd ⟨h, hy⟩ c3
              · exact ⟨h, hy⟩
          rw [if_pos c4]
          have := (e3 _ c4.1 _ c4.2).2
          simp only [s, hrr] at this
          exact this
  · intro hH
    have c1 : ¬ (i ∈ QO ∧ j ∈ Y) := fun h => hH (Or.inl ⟨Finset.mem_union_left _ h.1, h.2⟩)
    have c2 : ¬ (i ∈ QE ∧ j ∈ Y) := fun h => hH (Or.inl ⟨Finset.mem_union_right _ h.1, h.2⟩)
    have c3 : ¬ (Fin.rev j ∈ QO ∧ Fin.rev i ∈ Y) :=
      fun h => hH (Or.inr ⟨Finset.mem_union_left _ h.1, h.2⟩)
    have c4 : ¬ (Fin.rev j ∈ QE ∧ Fin.rev i ∈ Y) :=
      fun h => hH (Or.inr ⟨Finset.mem_union_right _ h.1, h.2⟩)
    rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4]

/-- The programs of the first `m` blocks. -/
theorem exists_col_programs (hn : 2 ≤ n) (lvO lvE : List CLevel) (L Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ)
    (hO : LevelsOK L lvO) (hE : LevelsOK L lvE)
    (hcO : CChain true lvO (fun _ => True) ColGoal) (hcE : CChain false lvE (fun _ => True) ColGoal)
    (ms : List (ℕ × ℕ)) (hmO : lvO.map CLevel.key = ms) (hmE : lvE.map CLevel.key = ms)
    (hp : ParamsOK n L Cslot sOf Tb ms) (S : ℕ) (hS0 : 0 < S) (hS : Even S)
    (π : Fin n → Fin n → Perm (Fin 24)) (m : ℕ) :
    ∃ P : Word n, (∀ m ∈ P, IsQ m) ∧
      P.length ≤ colRounds S sOf ms *
        (∑ t ∈ Finset.range m, (2 * (blockY n S t).card + 2 * Cslot)) ∧
      FixesSkel hn P ∧ ∀ i j, IsRow i → IsCol j →
        ((∃ t, t < m ∧ Handled n S t i j) → ColFull (Rv (rep i j) P * π i j)) ∧
        ((¬ ∃ t, t < m ∧ Handled n S t i j) → Rv (rep i j) P = 1) := by
  classical
  induction m with
  | zero => exact ⟨[], by simp, by simp, FixesSkel.nil hn, by simp⟩
  | succ m ih =>
    obtain ⟨P, p1, p2, p3, p4⟩ := ih
    obtain ⟨W, w1, w2, w3, w4⟩ := program_col hn lvO lvE L Cslot sOf Tb hO hE hcO hcE ms hmO hmE hp
      S hS (block_ctx (n := n) S m) (card_blockQ_le S m hS0) π
    refine ⟨P ++ W, ?_, ?_, p3.append w3, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact p1 x h
      · exact w1 x h
    · rw [Finset.sum_range_succ, Nat.mul_add, List.length_append]
      omega
    · intro i j hi hj
      obtain ⟨A1, A2⟩ := p4 i j hi hj
      obtain ⟨B1, B2⟩ := w4 i j hi hj
      rw [Rv_append]
      by_cases hH : Handled n S m i j
      · have hno : ¬ ∃ t, t < m ∧ Handled n S t i j := by
          rintro ⟨t, ht, h⟩
          have := handled_unique hi h hH
          omega
        rw [A2 hno, one_mul]
        exact ⟨fun _ => B1 hH, fun h => absurd ⟨m, by omega, hH⟩ h⟩
      · rw [B2 hH, mul_one]
        constructor
        · rintro ⟨t, ht, h⟩
          apply A1
          refine ⟨t, ?_, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | rfl
          · exact h'
          · exact absurd h hH
        · intro h
          exact A2 fun ⟨t, ht, h'⟩ => h ⟨t, by omega, h'⟩

/-! ### From orbits to the whole cube -/

theorem layerZ_ne_face (i : Fin n) : layerZ n i ≠ n ∧ layerZ n i ≠ -(n : ℤ) := by
  have := i.isLt
  simp only [layerZ]
  omega

/-- A word that fixes the skeleton and the orbits of the outer column, and that on each orbit of rows and
columns is either trivial or puts the colours right, makes every sticker the right colour. -/
theorem solved_of_orbits (hn : 3 ≤ n) (W : Word n) (hWQ : ∀ m ∈ W, IsQ m)
    (hrow : ∀ i j : Fin n, IsRow i → IsCol j →
      (∀ k, Word.eval W (e (rep i j) k) = e (rep i j) k) ∨
        ∃ σ : Perm (Fin 24), ColFull σ ∧ ∀ k, Word.eval W (e (rep i j) k) = e (rep i j) (σ k))
    (htop : ∀ i : Fin n, IsRow i → ∀ k, Word.eval W (e (rep i (layerOf hn 2)) k) =
      e (rep i (layerOf hn 2)) k)
    (hskel1 : ∀ k, Word.eval W (e (rep (row0 hn) (layerOf hn 2)) k) =
      e (rep (row0 hn) (layerOf hn 2)) k)
    (hskel2 : ∀ j : Fin n, layerZ n j = 0 → ∀ k, Word.eval W (e (rep (row0 hn) j) k) =
      e (rep (row0 hn) j) k)
    (hskel3 : ∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval W (e (rep m m) k) = e (rep m m) k) :
    ∀ q : Sticker n, faceOf ((Word.eval W)⁻¹ q) = faceOf q := by
  have hfix : ∀ q : Sticker n, Word.eval W q = q → faceOf ((Word.eval W)⁻¹ q) = faceOf q := by
    intro q hq
    have : (Word.eval W)⁻¹ q = q := by
      rw [Perm.inv_eq_iff_eq]
      exact hq.symm
    rw [this]
  intro q
  obtain ⟨k, ⟨i, j, hd, rfl⟩ | ⟨m, hm, rfl⟩⟩ := classify hn q
  · have hd1 := hd.1
    have hd2 := hd.2
    simp only [layerZ] at hd1 hd2
    have hjlt := j.isLt
    by_cases hi0 : i.val = 0
    · have hie : i = row0 hn := Fin.ext hi0
      subst hie
      apply hfix
      by_cases htopj : j = layerOf hn 2
      · subst htopj
        exact hskel1 k
      · by_cases hz : layerZ n j = 0
        · exact hskel2 j hz k
        · have hjv : j.val ≠ n - 1 := fun h => htopj (Fin.ext h)
          have hc : IsCoord n (-layerZ n j) := (isCoord_neg n _).2 (layerZ_isCoord j)
          obtain ⟨i', hi'⟩ := exists_layer hc
          have hpos : 0 < layerZ n j := by
            have : 0 ≤ layerZ n j := hd.2
            omega
          have hlt : layerZ n j < (n : ℤ) - 1 := by
            simp only [layerZ]; omega
          apply partner_fixed hn W hWQ j i' k hpos hlt hi'
          apply htop
          have hb := i'.isLt
          simp only [layerZ] at hi' hpos hlt
          simp only [IsRow]
          omega
    · have hri : IsRow i := by simp only [IsRow]; omega
      have hcj : IsCol j := by simp only [IsCol]; omega
      rcases hrow i j hri hcj with h | h
      · exact hfix _ (h k)
      · obtain ⟨σ, hσ, hact⟩ := h
        have hn0 : 0 < n := by omega
        have hinv : (Word.eval W)⁻¹ (e (rep i j) k) = e (rep i j) (σ⁻¹ k) := by
          rw [Perm.inv_eq_iff_eq, hact]
          simp
        rw [hinv, faceOf_e i j (layerZ_ne_face i) (layerZ_ne_face j) hn0,
          faceOf_e i j (layerZ_ne_face i) (layerZ_ne_face j) hn0]
        exact hσ k
  · exact hfix _ (hskel3 m hm k)

/-! ### The solver -/

/-- **Every coloured position is solved in `colouredW` quarter turns**, given chains. -/
theorem solve_of_chains (hn : 3 ≤ n) (lvO lvE : List CLevel) (L Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ)
    (hO : LevelsOK L lvO) (hE : LevelsOK L lvE)
    (hcO : CChain true lvO (fun _ => True) ColGoal) (hcE : CChain false lvE (fun _ => True) ColGoal)
    (ms : List (ℕ × ℕ)) (hmO : lvO.map CLevel.key = ms) (hmE : lvE.map CLevel.key = ms)
    (hp : ParamsOK n L Cslot sOf Tb ms) (S : ℕ) (hS0 : 0 < S) (hS : Even S)
    (g : Perm (Sticker n)) (hg : g ∈ cubeGroup n) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ colouredW n S Cslot sOf ms ∧
      IsSolved (colouring (Word.eval w * g)) := by
  classical
  have hn2 : 2 ≤ n := by omega
  obtain ⟨w₀, hw₀, rfl⟩ := word_of_mem g hg
  obtain ⟨Wp, a₁, ha₁, hpQ, ha₁Q, hplen, ha₁E, hskC, hskE, hskZ⟩ := exists_prep hn w₀ hw₀
  let π₀ : Fin n → Fin n → Perm (Fin 24) := fun i j => Rv (rep i j) a₁
  let π : Fin n → Fin n → Perm (Fin 24) := fun i j => (Rv (rep i j) a₁)⁻¹
  have hπ : ∀ i j, Perm.sign (π i j) = 1 := fun i j => by
    simp only [π]
    rw [Perm.sign_inv]
    exact sign_Rv _ _ ha₁E
  obtain ⟨P, p1, p2, p3, p4⟩ := exists_col_programs hn2 lvO lvE L Cslot sOf Tb hO hE hcO hcE ms hmO
    hmE hp S hS0 hS π₀ ((n / 2 - 1) / S + 1)
  have hun := fun i j => universal (π i j) (hπ i j)
  choose T hT1 hT2 using hun
  obtain ⟨Wb, b1, b2, b3, b4⟩ := exists_cleanup hn2 T hT1 (badOrbits n S).toList
    (Finset.nodup_toList _) (fun p hp => by
      obtain ⟨x, y⟩ := p
      have := mem_badOrbits.1 (Finset.mem_toList.1 hp)
      exact ⟨this.1, this.2.1⟩)
  rw [Finset.length_toList] at b2
  have hcard := card_badOrbits_le hn2 S hS0
  have hsum : (∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), (2 * (blockY n S t).card + 2 * Cslot)) ≤
      (n / 2 - 1) ^ 2 / S + 2 * ((n / 2 - 1) / S + 1) * Cslot := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h1 : ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * (blockY n S t).card ≤
        ∑ t ∈ Finset.range ((n / 2 - 1) / S + 1), 2 * ((n / 2 - 1) - (t + 1) * S) :=
      Finset.sum_le_sum fun t _ => Nat.mul_le_mul_left _ (card_blockY_le S t hS0)
    have h2 := sum_blocks_le S hS0 (n / 2 - 1)
    have h3 : ((n / 2 - 1) / S + 1) * (2 * Cslot) = 2 * ((n / 2 - 1) / S + 1) * Cslot := by ring
    omega
  have hPlen : P.length ≤ colRounds S sOf ms *
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
  · simp only [colouredW, List.length_append]
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
    -- the orbits that no program handles are solved exactly
    have hbad : ∀ i j : Fin n, IsRow i → IsCol j →
        (¬ ∃ t, t < (n / 2 - 1) / S + 1 ∧ Handled n S t i j) → ∀ k,
        Word.eval ((Wb ++ P) ++ a₁) (e (rep i j) k) = e (rep i j) k := by
      intro i j hi hj hH k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [word_Rv _ a₁ ha₁Q, word_Rv _ P p1]
      obtain ⟨_, A2⟩ := p4 i j hi hj
      have hb : (i, j) ∈ (badOrbits n S).toList := Finset.mem_toList.2
        (mem_badOrbits.2 ⟨hi, hj, fun h => hH ((exists_handled_iff hi).2 h)⟩)
      rw [A2 hH, Perm.one_apply, (b4 i j hi hj _).1 hb, hT2]
      simp [π]
    have hsolved : ∀ q : Sticker n,
        faceOf ((Word.eval ((Wb ++ P) ++ a₁))⁻¹ q) = faceOf q := by
      apply solved_of_orbits hn _ hWQ
      · intro i j hi hj
        by_cases hH : ∃ t, t < (n / 2 - 1) / S + 1 ∧ Handled n S t i j
        · right
          have hgood := (exists_handled_iff hi).1 hH
          have hnb : (i, j) ∉ (badOrbits n S).toList := fun h =>
            (mem_badOrbits.1 (Finset.mem_toList.1 h)).2.2 hgood
          refine ⟨Rv (rep i j) P * π₀ i j, (p4 i j hi hj).1 hH, fun k => ?_⟩
          simp only [Word.eval_append, Perm.mul_apply]
          rw [word_Rv _ a₁ ha₁Q, word_Rv _ P p1]
          exact (b4 i j hi hj _).2 hnb
        · left
          exact hbad i j hi hj hH
      · intro i hi
        apply hbad i _ hi
        · simp only [IsCol, layerOf]; omega
        · intro hH
          have hgood := (exists_handled_iff hi).1 hH
          have := mem_rowsF.1 hgood.1
          simp only [IsRow, layerOf, Fin.val_rev] at this
          omega
      · intro k
        rw [Word.eval_append, Perm.mul_apply, hskC k]
        exact hfS.1 (layerOf hn 2) (Or.inl rfl) k
      · intro j hj k
        rw [Word.eval_append, Perm.mul_apply, hskE j hj k]
        exact hfS.1 j (Or.inr hj) k
      · intro m hm k
        rw [Word.eval_append, Perm.mul_apply, hskZ m hm k]
        exact hfS.2 m hm k
    intro q q' hqq
    show faceOf _ = faceOf _
    rw [hsolved q, hsolved q']
    exact hqq

/-- **Upper bound on the coloured cube**, for abstract chains. -/
theorem godColoured_le_of_chains (μ : Metric) (hn : 3 ≤ n) (lvO lvE : List CLevel) (L Cslot : ℕ)
    (sOf Tb : ℕ × ℕ → ℕ) (hO : LevelsOK L lvO) (hE : LevelsOK L lvE)
    (hcO : CChain true lvO (fun _ => True) ColGoal) (hcE : CChain false lvE (fun _ => True) ColGoal)
    (ms : List (ℕ × ℕ)) (hmO : lvO.map CLevel.key = ms) (hmE : lvE.map CLevel.key = ms)
    (hp : ParamsOK n L Cslot sOf Tb ms) (S : ℕ) (hS0 : 0 < S) (hS : Even S) :
    godColoured μ n ≤ colouredW n S Cslot sOf ms := by
  apply Nat.sInf_le
  intro g hg
  obtain ⟨w, h1, h2, h3⟩ := solve_of_chains hn lvO lvE L Cslot sOf Tb hO hE hcO hcE ms hmO hmE hp S
    hS0 hS g hg
  exact ⟨w, fun m hm => allows_of_isQ μ m (h1 m hm), h2, h3⟩

/-! ### The finite data -/

/-- **The finite data of the coloured scheme.** `stepsO` is the family with `x = eT t`, `eM t`, and
`stepsE` the family with `x = (eT t)⁻¹`, `(eM t)⁻¹`, both in time order. `L` bounds the templates. -/
structure ColourData where
  stepsO : List ColStep
  stepsE : List ColStep
  L : ℕ

/-- The levels of the family `QO`. -/
def ColourData.lvO (D : ColourData) : List CLevel := famLevels D.stepsO ([], [])

/-- The levels of the family `QE`. -/
def ColourData.lvE (D : ColourData) : List CLevel := famLevels D.stepsE ([], [])

/-- The keys `(m, w)` of the levels of the data. -/
def ColourData.keys (D : ColourData) : List (ℕ × ℕ) := D.lvO.map CLevel.key

/-- The Boolean check of a family's levels. -/
def levelsCheck (L : ℕ) (lv : List CLevel) : Bool :=
  lv.all fun v => decide (0 < v.w) && decide (v.w < v.l.length) &&
    v.l.all fun t => decide (tmplLen t ≤ L)

/-- **The Boolean check of the data.** The two families must have the same keys. -/
def ColourData.check (D : ColourData) : Bool :=
  famCheck true D.stepsO ([], []) && famCheck false D.stepsE ([], []) &&
    (D.lvE.map CLevel.key == D.keys) && levelsCheck D.L D.lvO && levelsCheck D.L D.lvE

/-- The statements of the check, as a proposition. -/
structure ColourData.Valid (D : ColourData) : Prop where
  famO : famCheck true D.stepsO ([], []) = true
  famE : famCheck false D.stepsE ([], []) = true
  keys_eq : D.lvE.map CLevel.key = D.keys
  levelsO : levelsCheck D.L D.lvO = true
  levelsE : levelsCheck D.L D.lvE = true

theorem ColourData.valid_of_check {D : ColourData} (h : D.check = true) : D.Valid := by
  simp only [ColourData.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem levelsOK_of_check {L : ℕ} {lv : List CLevel} (h : levelsCheck L lv = true) :
    LevelsOK L lv := by
  simp only [levelsCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  intro v hv
  obtain ⟨⟨h1, h2⟩, h3⟩ := h v hv
  exact ⟨h1, h2.le, h3⟩

/-- All keys of valid data have `0 < w < m`. -/
theorem ColourData.Valid.keys_lt {D : ColourData} (h : D.Valid) :
    ∀ k ∈ D.keys, 0 < k.2 ∧ k.2 < k.1 := by
  intro k hk
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
  have := h.levelsO
  simp only [levelsCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨h1, h2⟩, _⟩ := this v hv
  exact ⟨h1, h2⟩

/-- The start of a family: nothing placed. -/
theorem chain_start {d : Bool} {steps : List ColStep} (h : famCheck d steps ([], []) = true) :
    CChain d (famLevels steps ([], [])) (fun _ => True) ColGoal := by
  cases hl : famLevels steps ([], []) with
  | nil =>
    have := famChain d steps _ h
    rw [hl] at this
    intro s _
    exact this s ⟨by simp [ColOK], by simp [ColOK]⟩
  | cons v t =>
    have := famChain d steps _ h
    rw [hl] at this
    obtain ⟨P', h1, h2⟩ := this
    exact ⟨P', fun s _ => h1 s ⟨by simp [ColOK], by simp [ColOK]⟩, h2⟩

/-- **The bound on God's number of the coloured cube, for valid data.** -/
theorem godColoured_le_colouredW (μ : Metric) (hn : 3 ≤ n) (D : ColourData) (hD : D.Valid)
    (S Cslot : ℕ) (sOf Tb : ℕ × ℕ → ℕ) (hS0 : 0 < S) (hS : Even S)
    (hp : ParamsOK n D.L Cslot sOf Tb D.keys) :
    godColoured μ n ≤ colouredW n S Cslot sOf D.keys :=
  godColoured_le_of_chains μ hn D.lvO D.lvE D.L Cslot sOf Tb (levelsOK_of_check hD.levelsO)
    (levelsOK_of_check hD.levelsE) (chain_start hD.famO) (chain_start hD.famE) D.keys rfl hD.keys_eq
    hp S hS0 hS

end RubiksGN
