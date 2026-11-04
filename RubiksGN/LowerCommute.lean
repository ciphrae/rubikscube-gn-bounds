import RubiksGN.LowerLabelled

/-!
# Fewer positions within `k` moves: moves on one axis commute

Moves on the same axis commute, so a word may be rewritten with the layers of each run of same-axis moves
strictly decreasing, merging moves on the same layer. Counting these normal forms with a transfer matrix
gives at most

```text
2 (c n) ^ k        c = 7.4 (htm), c = 5 (qtm)
```

permutations within `k` moves, instead of `(9n+1)^k`. The critical growth rate is the `y` with
`(1 + 3/y)^n = 3/2`, so `y → 3n / ln(3/2) ≈ 7.399 n` (htm), and `(1 + 1/y)^(2n) = 3/2`, so
`y → 2n / ln(3/2) ≈ 4.933 n` (qtm, where a half turn of a layer costs two quarter turns).

The limit constants do not change. The lower-order correction does: `log₂ n + 3.18` becomes
`log₂ n + 2.89` (and `log₂ n + 2.33` in `qtm`), for every `n ≥ 3`.
-/

open Equiv

namespace RubiksGN

open Classical

variable {n : ℕ}

/-! ### Relations between moves of one axis -/

theorem quarter_disjoint (a : Axis) (i j : Fin n) (h : i ≠ j) :
    Perm.Disjoint (quarter n a i) (quarter n a j) := by
  intro q
  by_cases hq : clamp n (a.coord q.1) = layerZ n i
  · right
    apply slice_apply_not
    intro h2
    exact h (layerZ_inj _ _ (hq.symm.trans h2))
  · left
    exact slice_apply_not _ _ _ _ hq

theorem rx_four (a : Axis) : mul (mul (mul (rx a) (rx a)) (rx a)) (rx a) = 0 := by
  cases a <;> decide +kernel

theorem quarter_of (a : Axis) (i : Fin n) (q : Sticker n)
    (h : clamp n (a.coord q.1) = layerZ n i) :
    quarter n a i q = actPerm n (rx a) q ∧
      clamp n (a.coord (actPerm n (rx a) q).1) = layerZ n i := by
  refine ⟨slice_apply_of _ _ _ _ h, ?_⟩
  rw [actPerm_val, coord_rx]
  exact h

/-- Four quarter turns of a layer are the identity. -/
theorem quarter_four (a : Axis) (i : Fin n) :
    quarter n a i * (quarter n a i * (quarter n a i * quarter n a i)) = 1 := by
  ext q : 1
  simp only [Perm.mul_apply, Perm.one_apply]
  by_cases hq : clamp n (a.coord q.1) = layerZ n i
  · obtain ⟨e1, h1⟩ := quarter_of a i q hq
    obtain ⟨e2, h2⟩ := quarter_of a i _ h1
    obtain ⟨e3, h3⟩ := quarter_of a i _ h2
    obtain ⟨e4, _⟩ := quarter_of a i _ h3
    rw [e1, e2, e3, e4]
    apply Subtype.ext
    simp only [actPerm_val]
    rw [← act_mul, ← act_mul, ← act_mul, rx_four, act_zero]
  · have e1 : quarter n a i q = q := slice_apply_not _ _ _ _ hq
    rw [e1, e1, e1, e1]

/-- The composition of two turns of one layer. -/
def turnAdd : Turn → Turn → Option Turn
  | .cw, .cw => some .half
  | .cw, .half => some .ccw
  | .cw, .ccw => none
  | .half, .cw => some .ccw
  | .half, .half => none
  | .half, .ccw => some .cw
  | .ccw, .cw => none
  | .ccw, .half => some .cw
  | .ccw, .ccw => some .half

theorem toPerm_add_some (a : Axis) (i : Fin n) (t t' s : Turn) (h : turnAdd t t' = some s) :
    Move.toPerm ((a, i, t) : Move n) * Move.toPerm ((a, i, t') : Move n) =
      Move.toPerm ((a, i, s) : Move n) := by
  have G := quarter_four a i
  set g := quarter n a i with hg
  have hinv : g⁻¹ = g * (g * g) := (eq_inv_of_mul_eq_one_left (by
    rw [_root_.mul_assoc]; exact G)).symm
  cases t <;> cases t' <;> simp only [turnAdd, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [Move.toPerm, ← hg]
  · rw [hinv]
  · rw [hinv, _root_.mul_assoc]
  · simp
  · simp
  · rw [hinv]
    calc g * (g * g) * (g * (g * g)) = g * g * (g * (g * (g * g))) := by
          simp only [_root_.mul_assoc]
      _ = g * g := by rw [G, mul_one]

theorem toPerm_add_none (a : Axis) (i : Fin n) (t t' : Turn) (h : turnAdd t t' = none) :
    Move.toPerm ((a, i, t) : Move n) * Move.toPerm ((a, i, t') : Move n) = 1 := by
  have G := quarter_four a i
  cases t <;> cases t' <;> simp only [turnAdd, reduceCtorEq] at h <;> simp only [Move.toPerm]
  · simp
  · rw [_root_.mul_assoc]; exact G
  · simp

theorem toPerm_commute (a : Axis) (i j : Fin n) (h : i ≠ j) (t t' : Turn) :
    Commute (Move.toPerm ((a, i, t) : Move n)) (Move.toPerm ((a, j, t') : Move n)) := by
  have c : Commute (quarter n a i) (quarter n a j) := (quarter_disjoint a i j h).commute
  have c1 : Commute (Move.toPerm ((a, i, t) : Move n)) (quarter n a j) := by
    cases t
    · exact c
    · exact c.mul_left c
    · exact c.inv_left
  cases t'
  · exact c1
  · exact c1.mul_right c1
  · exact c1.inv_right

/-! ### Normal forms -/

/-- `m'` may follow `m`: another axis, or a strictly lower layer of the same axis. -/
def Follow (m m' : Move n) : Prop := m.1 ≠ m'.1 ∨ m'.2.1 < m.2.1

/-- The first move of a word may follow `x`. -/
def Hd (x : Move n) : Word n → Prop
  | [] => True
  | y :: _ => Follow x y

/-- Words in normal form. -/
def Normal : Word n → Prop
  | [] => True
  | m :: t => Hd m t ∧ Normal t

/-- The cost of a turn: a half turn is two quarter turns in `qtm`. -/
def wt : Metric → Turn → ℕ
  | .htm, _ => 1
  | .qtm, .half => 2
  | .qtm, .cw => 1
  | .qtm, .ccw => 1

/-- The cost of a word. -/
def cost (μ : Metric) (w : Word n) : ℕ := (w.map fun m => wt μ m.2.2).sum

@[simp] theorem cost_nil (μ : Metric) : cost μ ([] : Word n) = 0 := rfl

@[simp] theorem cost_cons (μ : Metric) (m : Move n) (t : Word n) :
    cost μ (m :: t) = wt μ m.2.2 + cost μ t := by
  simp [cost]

theorem wt_pos (μ : Metric) (t : Turn) : 1 ≤ wt μ t := by
  cases μ <;> cases t <;> simp [wt]

theorem wt_add (μ : Metric) (t t' s : Turn) (h : turnAdd t t' = some s) :
    wt μ s ≤ wt μ t + wt μ t' := by
  cases μ <;> cases t <;> cases t' <;> simp only [turnAdd, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp [wt]

/-- A word allowed by a metric costs its length. -/
theorem cost_of_allows (μ : Metric) : ∀ w : Word n, (∀ m ∈ w, μ.allows m) → cost μ w = w.length
  | [], _ => rfl
  | m :: t, h => by
    have h1 : wt μ m.2.2 = 1 := by
      have hm : μ.allows m := h m (List.mem_cons_self ..)
      obtain ⟨a, i, u⟩ := m
      cases μ
      · rfl
      · cases u
        · rfl
        · exact absurd rfl hm
        · rfl
    rw [cost_cons, h1, cost_of_allows μ t (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp only [List.length_cons]
    omega

/-- Inserting one move into a normal form. -/
theorem exists_insert (μ : Metric) (m : Move n) : ∀ w : Word n, Normal w →
    ∃ w' : Word n, Normal w' ∧ Word.eval w' = m.toPerm * Word.eval w ∧
      cost μ w' ≤ wt μ m.2.2 + cost μ w ∧
      ∀ x : Move n, x.1 = m.1 → m.2.1 < x.2.1 → Hd x w → Hd x w' := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨[m], ⟨trivial, trivial⟩, by simp, by simp, ?_⟩
    intro x _ h2 _
    exact Or.inr h2
  | cons m' t ih =>
    rintro ⟨h1, h2⟩
    by_cases hF : Follow m m'
    · refine ⟨m :: m' :: t, ⟨hF, h1, h2⟩, by simp, by simp, ?_⟩
      intro x _ hlt _
      exact Or.inr hlt
    · have hax : m.1 = m'.1 := by
        by_contra hne
        exact hF (Or.inl hne)
      have hle : m.2.1 ≤ m'.2.1 := by
        by_contra hne
        exact hF (Or.inr (not_le.1 hne))
      obtain ⟨a, i, u⟩ := m
      obtain ⟨a', i', u'⟩ := m'
      obtain rfl : a = a' := hax
      rcases lt_or_eq_of_le hle with hlt | heq
      · -- commute `m'` to the front
        obtain ⟨t'', h3, h4, h5, h6⟩ := ih h2
        refine ⟨(a, i', u') :: t'', ⟨h6 _ rfl hlt h1, h3⟩, ?_, ?_, ?_⟩
        · simp only [Word.eval_cons, h4]
          rw [← _root_.mul_assoc, ← _root_.mul_assoc,
            (toPerm_commute a i' i (ne_of_gt hlt) u' u).eq]
        · simp only [cost_cons] at h5 ⊢
          omega
        · intro x _ _ hx
          exact hx
      · obtain rfl : i = i' := heq
        cases hadd : turnAdd u u' with
        | none =>
          refine ⟨t, h2, ?_, ?_, ?_⟩
          · simp only [Word.eval_cons]
            rw [← _root_.mul_assoc, toPerm_add_none a i u u' hadd, one_mul]
          · simp only [cost_cons]
            omega
          · intro x hx1 hx2 _
            cases t with
            | nil => trivial
            | cons y s =>
              rcases h1 with hy | hy
              · exact Or.inl (fun hxy => hy (hx1.symm.trans hxy))
              · exact Or.inr (lt_trans hy hx2)
        | some s =>
          refine ⟨(a, i, s) :: t, ⟨?_, h2⟩, ?_, ?_, ?_⟩
          · cases t with
            | nil => trivial
            | cons y _ => exact h1
          · simp only [Word.eval_cons]
            rw [← _root_.mul_assoc, toPerm_add_some a i u u' s hadd]
          · have := wt_add μ u u' s hadd
            simp only [cost_cons]
            omega
          · intro x _ _ hx
            exact hx

/-- Every word has a normal form of no larger cost. -/
theorem exists_normal (μ : Metric) (w : Word n) :
    ∃ w' : Word n, Normal w' ∧ Word.eval w' = Word.eval w ∧ cost μ w' ≤ cost μ w := by
  induction w with
  | nil => exact ⟨[], trivial, rfl, le_rfl⟩
  | cons m t ih =>
    obtain ⟨t', h1, h2, h3⟩ := ih
    obtain ⟨w', a1, a2, a3, _⟩ := exists_insert μ m t' h1
    refine ⟨w', a1, ?_, ?_⟩
    · rw [a2, h2, Word.eval_cons]
    · rw [cost_cons]
      omega

/-! ### Sums over moves -/

theorem sum_axis (g : Axis → ℝ) : ∑ a, g a = g .x + g .y + g .z := by
  change ({.x, .y, .z} : Finset Axis).sum g = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem sum_turn (g : Turn → ℝ) : ∑ a, g a = g .cw + g .half + g .ccw := by
  change ({.cw, .half, .ccw} : Finset Turn).sum g = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem sum_axis_two (a₀ : Axis) (A B : ℝ) (g : Axis → ℝ) (hA : g a₀ = A)
    (hB : ∀ a, a ≠ a₀ → g a = B) : ∑ a, g a = A + 2 * B := by
  rw [sum_axis]
  cases a₀
  · rw [hA, hB .y (by decide), hB .z (by decide)]; ring
  · rw [hA, hB .x (by decide), hB .z (by decide)]; ring
  · rw [hA, hB .x (by decide), hB .y (by decide)]; ring

/-- The weight of one layer, with `u` the weight of one unit of cost. -/
noncomputable def tau (μ : Metric) (u : ℝ) : ℝ := ∑ t : Turn, u ^ wt μ t

theorem tau_htm (u : ℝ) : tau .htm u = 3 * u := by
  simp only [tau, sum_turn, wt]
  ring

theorem tau_qtm (u : ℝ) : tau .qtm u = 2 * u + u ^ 2 := by
  simp only [tau, sum_turn, wt]
  ring

theorem tau_nonneg (μ : Metric) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ tau μ u :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hu _

/-- The partial geometric sum of the weights of the layers below `l`. -/
theorem sum_below (τ : ℝ) (l : ℕ) (hl : l ≤ n) (Q : Fin n → Prop)
    (hQ : ∀ i, Q i ↔ i.val < l) :
    (∑ i : Fin n, if Q i then (τ + 1) ^ i.val else 0) * τ = (τ + 1) ^ l - 1 := by
  have h1 : (∑ i : Fin n, if Q i then (τ + 1) ^ i.val else 0) =
      ∑ i : Fin n, (fun j : ℕ => if j < l then (τ + 1) ^ j else 0) i.val := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : Q i
    · simp [h, (hQ i).1 h]
    · have : ¬ i.val < l := fun h2 => h ((hQ i).2 h2)
      simp [h, this]
  rw [h1, Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < l then (τ + 1) ^ j else 0) n,
    ← Finset.sum_filter]
  have h2 : (Finset.range n).filter (· < l) = Finset.range l := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h2]
  have := geom_sum_mul_add τ l
  linarith

theorem sum_P (τ : ℝ) (a₀ : Axis) (l : ℕ) (hl : l ≤ n) (P : Axis → Fin n → Prop)
    (h1 : ∀ i, P a₀ i ↔ i.val < l) (h2 : ∀ a, a ≠ a₀ → ∀ i, P a i) :
    ∑ a : Axis, (∑ i : Fin n, if P a i then (τ + 1) ^ i.val else 0) * τ =
      (τ + 1) ^ l - 1 + 2 * ((τ + 1) ^ n - 1) :=
  sum_axis_two a₀ _ _ _ (sum_below τ l hl _ h1)
    (fun a ha => sum_below τ n le_rfl _ fun i => iff_of_true (h2 a ha i) i.isLt)

theorem sum_moves (μ : Metric) (u : ℝ) (φ : Fin n → ℝ) (P : Axis → Fin n → Prop) :
    ∑ m : Move n, (if P m.1 m.2.1 then φ m.2.1 * u ^ wt μ m.2.2 else 0) =
      ∑ a : Axis, (∑ i : Fin n, if P a i then φ i else 0) * tau μ u := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : P a i
  · simp only [h, if_true, tau, Finset.mul_sum]
  · simp [h]

/-! ### The transfer-matrix count -/

/-- The bound for normal words of cost exactly `k` that may follow a given move. -/
def HeadBound (μ : Metric) (n : ℕ) (y : ℝ) (k : ℕ) : Prop :=
  ∀ h : Move n, ∃ F : Finset (Word n), (∀ w, Hd h w → Normal w → cost μ w = k → w ∈ F) ∧
    (F.card : ℝ) ≤ (tau μ y⁻¹ + 1) ^ h.2.1.val * y ^ k

/-- One step of the recursion: choose the first move, among those allowed by `P`. -/
theorem step (μ : Metric) {y : ℝ} (hy : 0 < y) (k : ℕ) (hk : 0 < k)
    (IH : ∀ k' < k, HeadBound μ n y k') (P : Axis → Fin n → Prop) :
    ∃ F : Finset (Word n),
      (∀ (m : Move n) (t : Word n), P m.1 m.2.1 → Hd m t → Normal t → cost μ (m :: t) = k →
        m :: t ∈ F) ∧
      (F.card : ℝ) ≤ y ^ k * ∑ a : Axis,
        (∑ i : Fin n, if P a i then (tau μ y⁻¹ + 1) ^ i.val else 0) * tau μ y⁻¹ := by
  have ih' := fun m : Move n =>
    IH (k - wt μ m.2.2) (by have := wt_pos μ m.2.2; omega) m
  choose G hG1 hG2 using ih'
  let M : Finset (Move n) := Finset.univ.filter fun m => P m.1 m.2.1 ∧ wt μ m.2.2 ≤ k
  refine ⟨M.biUnion fun m => (G m).image fun t => m :: t, ?_, ?_⟩
  · intro m t hP hH hN hc
    rw [cost_cons] at hc
    refine Finset.mem_biUnion.2 ⟨m, ?_, Finset.mem_image.2 ⟨t, hG1 m t hH hN (by omega), rfl⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hP, by omega⟩
  · set u := y⁻¹ with hu
    have hu0 : 0 ≤ u := by positivity
    set φ : Fin n → ℝ := fun i => (tau μ u + 1) ^ i.val with hφ
    have hφ0 : ∀ i, 0 ≤ φ i := fun i => by
      have := tau_nonneg μ hu0
      simp only [hφ]
      positivity
    have h1 : ((M.biUnion fun m => (G m).image fun t => m :: t).card : ℝ) ≤
        ∑ m ∈ M, ((G m).card : ℝ) := by
      have : (M.biUnion fun m => (G m).image fun t => m :: t).card ≤ ∑ m ∈ M, (G m).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ => Finset.card_image_le)
      exact_mod_cast this
    have h2 : ∑ m ∈ M, ((G m).card : ℝ) ≤ ∑ m ∈ M, y ^ k * (φ m.2.1 * u ^ wt μ m.2.2) := by
      apply Finset.sum_le_sum
      intro m hm
      have hle : wt μ m.2.2 ≤ k := (Finset.mem_filter.1 hm).2.2
      have e : y ^ (k - wt μ m.2.2) = y ^ k * u ^ wt μ m.2.2 := by
        rw [pow_sub₀ y hy.ne' hle, hu, inv_pow]
      calc ((G m).card : ℝ) ≤ φ m.2.1 * y ^ (k - wt μ m.2.2) := hG2 m
        _ = _ := by rw [e]; ring
    have h3 : ∑ m ∈ M, y ^ k * (φ m.2.1 * u ^ wt μ m.2.2) ≤
        ∑ m : Move n, y ^ k * (if P m.1 m.2.1 then φ m.2.1 * u ^ wt μ m.2.2 else 0) := by
      have hpos : 0 ≤ y ^ k := by positivity
      have e : ∀ m ∈ M, y ^ k * (φ m.2.1 * u ^ wt μ m.2.2) =
          y ^ k * (if P m.1 m.2.1 then φ m.2.1 * u ^ wt μ m.2.2 else 0) := by
        intro m hm
        rw [if_pos (Finset.mem_filter.1 hm).2.1]
      rw [Finset.sum_congr rfl e]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro m _ _
      apply mul_nonneg hpos
      split_ifs
      · exact mul_nonneg (hφ0 _) (pow_nonneg hu0 _)
      · exact le_rfl
    have e3 : ∑ m : Move n, y ^ k * (if P m.1 m.2.1 then φ m.2.1 * u ^ wt μ m.2.2 else 0) =
        y ^ k * ∑ a : Axis, (∑ i : Fin n, if P a i then φ i else 0) * tau μ u := by
      rw [← Finset.mul_sum, sum_moves μ u φ P]
    exact h1.trans (h2.trans (h3.trans e3.le))

theorem cost_eq_zero (μ : Metric) : ∀ w : Word n, cost μ w = 0 → w = []
  | [], _ => rfl
  | m :: t, h => by
    rw [cost_cons] at h
    have := wt_pos μ m.2.2
    omega

/-- The transfer-matrix bound: `(τ + 1) ^ i` is a super-eigenvector, because `(τ + 1)^n ≤ 3/2`. -/
theorem head_bound (μ : Metric) {y : ℝ} (hy : 0 < y) (H : (tau μ y⁻¹ + 1) ^ n ≤ 3 / 2) (k : ℕ) :
    HeadBound μ n y k := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro h
    have hτ : 0 ≤ tau μ y⁻¹ := tau_nonneg μ (by positivity)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨{[]}, ?_, ?_⟩
      · intro w _ _ hc
        rw [cost_eq_zero μ w hc]
        exact Finset.mem_singleton_self _
      · simp only [Finset.card_singleton, Nat.cast_one, pow_zero, mul_one]
        exact one_le_pow₀ (by linarith)
    · obtain ⟨F, h1, h2⟩ := step μ hy k hk IH (fun a i => h.1 ≠ a ∨ i < h.2.1)
      refine ⟨F, ?_, ?_⟩
      · intro w hH hN hc
        cases w with
        | nil =>
          simp only [cost_nil] at hc
          omega
        | cons m t => exact h1 m t hH hN.1 hN.2 hc
      · refine h2.trans ?_
        have hsum := sum_P (tau μ y⁻¹) h.1 h.2.1.val h.2.1.isLt.le
          (fun a i => h.1 ≠ a ∨ i < h.2.1) (fun i => by simp only [ne_eq, not_true_eq_false,
            false_or, Fin.lt_def]) (fun a ha i => Or.inl (Ne.symm ha))
        rw [hsum, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

/-- The number of normal words of cost exactly `k > 0`. -/
theorem exact_bound (μ : Metric) {y : ℝ} (hy : 0 < y) (H : (tau μ y⁻¹ + 1) ^ n ≤ 3 / 2) (k : ℕ)
    (hk : 0 < k) : ∃ F : Finset (Word n), (∀ w, Normal w → cost μ w = k → w ∈ F) ∧
      (F.card : ℝ) ≤ 3 / 2 * y ^ k := by
  obtain ⟨F, h1, h2⟩ := step μ hy k hk (fun k' _ => head_bound μ hy H k') (fun _ _ => True)
  refine ⟨F, ?_, ?_⟩
  · intro w hN hc
    cases w with
    | nil =>
      simp only [cost_nil] at hc
      omega
    | cons m t => exact h1 m t trivial hN.1 hN.2 hc
  · refine h2.trans ?_
    have hsum := sum_P (tau μ y⁻¹) .x n le_rfl (fun _ _ => True)
      (fun i => iff_of_true trivial i.isLt) (fun _ _ _ => trivial)
    rw [hsum, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith

/-- The number of normal words of cost at most `k`. -/
theorem le_bound (μ : Metric) {y : ℝ} (hy : 4 ≤ y) (H : (tau μ y⁻¹ + 1) ^ n ≤ 3 / 2) (k : ℕ) :
    ∃ F : Finset (Word n), (∀ w, Normal w → cost μ w ≤ k → w ∈ F) ∧ (F.card : ℝ) ≤ 2 * y ^ k := by
  have hy0 : 0 < y := by linarith
  induction k with
  | zero =>
    refine ⟨{[]}, ?_, by simp⟩
    intro w _ hc
    rw [cost_eq_zero μ w (by omega)]
    exact Finset.mem_singleton_self _
  | succ k ih =>
    obtain ⟨F, h1, h2⟩ := ih
    obtain ⟨E, h3, h4⟩ := exact_bound μ hy0 H (k + 1) (Nat.succ_pos k)
    refine ⟨F ∪ E, ?_, ?_⟩
    · intro w hN hc
      rcases Nat.lt_or_ge (cost μ w) (k + 1) with h | h
      · exact Finset.mem_union_left _ (h1 w hN (by omega))
      · exact Finset.mem_union_right _ (h3 w hN (by omega))
    · have hc : ((F ∪ E).card : ℝ) ≤ F.card + E.card := by
        exact_mod_cast Finset.card_union_le F E
      have hp : 0 ≤ y ^ k := by positivity
      rw [pow_succ] at h4 ⊢
      nlinarith

/-! ### The growth rates -/

/-- The growth rate per layer. -/
noncomputable def cMove : Metric → ℝ
  | .htm => 7.4
  | .qtm => 5

theorem exp_rat_le (p q : ℕ) (hq : q ≠ 0) (b : ℝ) (hb : 0 ≤ b)
    (h : (2.7182818286 : ℝ) ^ p ≤ b ^ q) : Real.exp ((p : ℝ) / q) ≤ b := by
  apply le_of_pow_le_pow_left₀ hq hb
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [← Real.exp_nat_mul]
  have e : (q : ℝ) * ((p : ℝ) / q) = (p : ℝ) * 1 := by field_simp
  rw [e, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le p).trans h

theorem pow_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : (x + 1) ^ k ≤ Real.exp ((k : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp x) k

theorem growth (μ : Metric) (hn : 1 ≤ n) : (tau μ (cMove μ * n)⁻¹ + 1) ^ n ≤ 3 / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  cases μ with
  | htm =>
    rw [tau_htm]
    have hx : 0 ≤ 3 * (cMove .htm * (n : ℝ))⁻¹ := by
      simp only [cMove]
      positivity
    refine (pow_le_exp _ hx n).trans ?_
    have e : (n : ℝ) * (3 * (cMove .htm * (n : ℝ))⁻¹) = ((15 : ℕ) : ℝ) / (37 : ℕ) := by
      simp only [cMove]
      field_simp
      norm_num
    rw [e]
    exact exp_rat_le 15 37 (by norm_num) _ (by norm_num) (by norm_num)
  | qtm =>
    rw [tau_qtm]
    set u := (cMove .qtm * (n : ℝ))⁻¹ with hu
    have hu0 : 0 ≤ u := by
      simp only [hu, cMove]
      positivity
    have e1 : 2 * u + u ^ 2 + 1 = (u + 1) ^ 2 := by ring
    rw [e1, ← pow_mul, mul_comm 2 n]
    refine (pow_le_exp _ hu0 _).trans ?_
    have e : ((n * 2 : ℕ) : ℝ) * u = ((2 : ℕ) : ℝ) / (5 : ℕ) := by
      simp only [hu, cMove]
      push_cast
      field_simp
    rw [e]
    exact exp_rat_le 2 5 (by norm_num) _ (by norm_num) (by norm_num)

theorem cMove_ge (μ : Metric) : 5 ≤ cMove μ := by
  cases μ <;> simp only [cMove] <;> norm_num

/-! ### The improved count of reachable permutations -/

/-- A family of at most `2 (c n)^k` words realising everything reachable within `k` moves. -/
theorem reach_cover (μ : Metric) (hn : 1 ≤ n) (k : ℕ) :
    ∃ F : Finset (Word n), (F.card : ℝ) ≤ 2 * (cMove μ * n) ^ k ∧
      ∀ w : Word n, (∀ m ∈ w, μ.allows m) → w.length ≤ k →
        ∃ w' ∈ F, Word.eval w' = Word.eval w := by
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 4 ≤ cMove μ * n := by nlinarith [cMove_ge μ]
  obtain ⟨F, h1, h2⟩ := le_bound μ hy (growth μ hn) k
  refine ⟨F, h2, ?_⟩
  intro w hw hl
  obtain ⟨w', a1, a2, a3⟩ := exists_normal μ w
  exact ⟨w', h1 w' a1 (by rw [cost_of_allows μ w hw] at a3; omega), a2⟩

/-- The permutations reachable within `k` moves. -/
def reach (μ : Metric) (n k : ℕ) : Set (Perm (Sticker n)) :=
  {g | ∃ w : Word n, (∀ m ∈ w, μ.allows m) ∧ w.length ≤ k ∧ Word.eval w = g}

/-- **At most `2 (c n)^k` permutations lie within `k` moves.** (`c = 7.4` in `htm`, `c = 5` in `qtm`.) -/
theorem ncard_reach_le (μ : Metric) (hn : 1 ≤ n) (k : ℕ) :
    ((reach μ n k).ncard : ℝ) ≤ 2 * (cMove μ * n) ^ k := by
  obtain ⟨F, h1, h2⟩ := reach_cover μ hn k
  have hsub : reach μ n k ⊆ Word.eval '' (F : Set (Word n)) := by
    rintro g ⟨w, hw, hl, rfl⟩
    obtain ⟨w', a1, a2⟩ := h2 w hw hl
    exact ⟨w', a1, a2⟩
  have hfin : (Word.eval '' (F : Set (Word n))).Finite := F.finite_toSet.image _
  have h3 : (reach μ n k).ncard ≤ F.card :=
    (Set.ncard_le_ncard hsub hfin).trans
      ((Set.ncard_image_le F.finite_toSet).trans (Set.ncard_coe_finset F).le)
  exact le_trans (by exact_mod_cast h3) h1

/-! ### The counting bounds -/

/-- The improved counting bound for the coloured cube. -/
theorem count_coloured_commute (hn : 3 ≤ n) (μ : Metric) (K : ℕ) (hK : ColouredSolvable μ n K) :
    (Zval : ℝ) ^ innerOrbits n ≤ 6 ^ 6 * (2 * (cMove μ * n) ^ K) := by
  choose g hg1 hg2 using realise (n := n) hn
  obtain ⟨F₀, hF₀, hcov⟩ := reach_cover μ (by omega : 1 ≤ n) K
  have hsol : ∀ F : Inner n → Bal, ∃ (φ : Fin 6 → Fin 6) (w : F₀),
      colouring (g F) = φ ∘ faceOf ∘ Word.eval w.1 := by
    intro F
    obtain ⟨w, h0, hlen, hs⟩ := hK (g F) (hg1 F)
    obtain ⟨φ, hφ⟩ := solved_factor _ hs
    obtain ⟨w', a1, a2⟩ := hcov w h0 hlen
    exact ⟨φ, ⟨w', a1⟩, by rw [a2]; exact colouring_factor _ _ _ hφ⟩
  choose φ w hfac using hsol
  let Ψ : (Inner n → Bal) → (Fin 6 → Fin 6) × F₀ := fun F => (φ F, w F)
  have hinj : Function.Injective Ψ := by
    intro F F' h
    have h1 : φ F = φ F' := congrArg Prod.fst h
    have h2 : w F = w F' := congrArg Prod.snd h
    have hc : colouring (g F) = colouring (g F') := by
      rw [hfac, hfac, h1, h2]
    funext p
    apply Subtype.ext
    funext k
    rw [← hg2 F p k, ← hg2 F' p k, hc]
  have hcard := Fintype.card_le_of_injective Ψ hinj
  have c1 : Fintype.card (Inner n → Bal) = Zval ^ innerOrbits n := by
    rw [Fintype.card_fun, Fintype.card_coe, card_Bal, card_Inner]
  have c2 : Fintype.card ((Fin 6 → Fin 6) × F₀) = 6 ^ 6 * F₀.card := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  rw [c1, c2] at hcard
  have hr : (Zval : ℝ) ^ innerOrbits n ≤ 6 ^ 6 * (F₀.card : ℝ) := by exact_mod_cast hcard
  exact hr.trans (mul_le_mul_of_nonneg_left hF₀ (by norm_num))

/-- The improved counting bound for the labelled cube. -/
theorem count_labelled_commute (hn : 3 ≤ n) (μ : Metric) (K : ℕ) (hK : LabelledSolvable μ n K) :
    (evenN : ℝ) ^ fullOrbits n ≤ 2 * (cMove μ * n) ^ K := by
  choose g hg1 hg2 using realiseL (n := n) (by omega)
  obtain ⟨F₀, hF₀, hcov⟩ := reach_cover μ (by omega : 1 ≤ n) K
  have hsol : ∀ F : Full n → alternatingGroup (Fin 24), ∃ w : F₀, Word.eval w.1 * g F = 1 := by
    intro F
    obtain ⟨w, h0, hlen, hs⟩ := hK (g F) (hg1 F)
    obtain ⟨w', a1, a2⟩ := hcov w h0 hlen
    exact ⟨⟨w', a1⟩, by rw [a2]; exact hs⟩
  choose w hw using hsol
  have hinj : Function.Injective w := by
    intro F F' h
    have hg : g F = g F' := by
      have a := hw F
      have b := hw F'
      rw [h] at a
      exact mul_left_cancel (a.trans b.symm)
    apply realiseL_inj (g := g F) (hg2 F)
    rw [hg]
    exact hg2 F'
  have hcard := Fintype.card_le_of_injective w hinj
  rw [Fintype.card_fun, card_alt, card_Full, Fintype.card_coe] at hcard
  have hr : (evenN : ℝ) ^ fullOrbits n ≤ (F₀.card : ℝ) := by exact_mod_cast hcard
  exact hr.trans hF₀

/-! ### The lower bounds with the improved lower-order term -/

theorem lg74_upper : lg 7.4 ≤ 2.89 := by
  have h : ((7.4 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 289 := by
    have hn : 37 ^ 100 ≤ 2 ^ 289 * 5 ^ 100 := by decide +kernel
    have hr : ((37 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 289 * (5 : ℝ) ^ 100 := by exact_mod_cast hn
    have e : (7.4 : ℝ) = 37 / 5 := by norm_num
    rw [e, div_pow, div_le_iff₀ (by positivity)]
    exact hr
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  push_cast at h2
  linarith

theorem lg5_upper : lg 5 ≤ 2.33 := by
  have h : ((5 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 233 := by
    exact_mod_cast (by decide +kernel : 5 ^ 100 ≤ 2 ^ 233)
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  push_cast at h2
  linarith

/-- `log₂ c`, rounded up. -/
noncomputable def dMove : Metric → ℝ
  | .htm => 2.89
  | .qtm => 2.33

theorem lg_cMove (μ : Metric) : lg (cMove μ) ≤ dMove μ := by
  cases μ
  · exact lg74_upper
  · exact lg5_upper

theorem dMove_le (μ : Metric) : dMove μ ≤ 2.89 := by
  cases μ <;> simp only [dMove] <;> norm_num

theorem dMove_pos (μ : Metric) : 0 < dMove μ := by
  cases μ <;> simp only [dMove] <;> norm_num

theorem cMove_pos (μ : Metric) : 0 < cMove μ := by
  have := cMove_ge μ
  linarith

theorem lg_cn_le (μ : Metric) (hn : 3 ≤ n) : lg (cMove μ * n) ≤ lg n + dMove μ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [lg_mul (cMove_pos μ).ne' hn0.ne']
  linarith [lg_cMove μ]

theorem lg_pos_of (hn : 3 ≤ n) : 0 < lg n :=
  Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1 < n))

/-- **Coloured cube, improved lower-order term.** For every `n ≥ 3`; `dMove` is `2.89` in `htm` and
`2.33` in `qtm`. -/
theorem lowerCommute_coloured (μ : Metric) (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (lg n + dMove μ) ≤ godColoured μ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc := count_coloured_commute hn μ _ (coloured_spec μ hn)
  have hZ : (0 : ℝ) < Zval := by
    rw [Zval_eq]; norm_num
  have hcn : 0 < cMove μ * n := mul_pos (cMove_pos μ) hn0
  have h2 := lg_mono (by positivity) hc
  rw [lg_pow, lg_mul (by positivity) (by positivity), lg_mul (by norm_num) (by positivity),
    lg_pow, lg_pow, lg_two] at h2
  push_cast at h2
  have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left (lg_cn_le μ hn) hG
  have hin := innerOrbits_lower hn
  have hI0 : (0 : ℝ) ≤ innerOrbits n := by positivity
  have h3 : (51.52 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 3) / 4) ≤ (innerOrbits n : ℝ) * lg Zval := by
    calc (51.52 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 3) / 4) ≤ 51.52 * (innerOrbits n : ℝ) :=
          mul_le_mul_of_nonneg_left hin (by norm_num)
      _ ≤ lg Zval * (innerOrbits n : ℝ) := mul_le_mul_of_nonneg_right LZ_lower hI0
      _ = _ := mul_comm _ _
  have h6 := lg6_upper
  rw [div_le_iff₀ (by linarith [lg_pos_of hn, dMove_pos μ])]
  nlinarith

/-- **Labelled cube, improved lower-order term.** -/
theorem lowerCommute_labelled (μ : Metric) (hn : 3 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (lg n + dMove μ) ≤ godLabelled μ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc := count_labelled_commute hn μ _ (labelled_spec μ hn)
  have hE : (0 : ℝ) < evenN := by
    have : 0 < evenN := by decide +kernel
    exact_mod_cast this
  have hcn : 0 < cMove μ * n := mul_pos (cMove_pos μ) hn0
  have h2 := lg_mono (by positivity) hc
  rw [lg_pow, lg_mul (by norm_num) (by positivity), lg_pow, lg_two] at h2
  have hG : (0 : ℝ) ≤ godLabelled μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left (lg_cn_le μ hn) hG
  have hin := fullOrbits_lower hn
  have hI0 : (0 : ℝ) ≤ fullOrbits n := by positivity
  have h3 : (78.036 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) - 3) / 4) ≤ (fullOrbits n : ℝ) * lg evenN := by
    calc (78.036 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) - 3) / 4) ≤ 78.036 * (fullOrbits n : ℝ) :=
          mul_le_mul_of_nonneg_left hin (by norm_num)
      _ ≤ lg evenN * (fullOrbits n : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [LE_lower, show LE = lg evenN from rfl]) hI0
      _ = _ := mul_comm _ _
  rw [div_le_iff₀ (by linarith [lg_pos_of hn, dMove_pos μ])]
  nlinarith

/-- `lowerCommute_coloured` in `htm`. -/
theorem lowerCommute_coloured_htm (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (lg n + 2.89) ≤ godColoured .htm n :=
  lowerCommute_coloured .htm hn

/-- `lowerCommute_coloured` in `qtm`. -/
theorem lowerCommute_coloured_qtm (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (lg n + 2.33) ≤ godColoured .qtm n :=
  lowerCommute_coloured .qtm hn

/-- `lowerCommute_labelled` in `htm`. -/
theorem lowerCommute_labelled_htm (hn : 3 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (lg n + 2.89) ≤ godLabelled .htm n :=
  lowerCommute_labelled .htm hn

/-- `lowerCommute_labelled` in `qtm`. -/
theorem lowerCommute_labelled_qtm (hn : 3 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (lg n + 2.33) ≤ godLabelled .qtm n :=
  lowerCommute_labelled .qtm hn

end RubiksGN
