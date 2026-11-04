import RubiksGN.SecondOrder

/-!
# A lower bound specific to the labelled cube

The coloured count of `Lower.lean` only sees `Z = 24!/(4!)⁶` arrangements per orbit. On the labelled cube
the word solving a position determines the position, and on each of the `(n/2 - 1)(n - n/2)` orbits
`rows × cols` (wings included) every even permutation of the 24 coordinates occurs, independently of the
other orbits. So

```text
(24!/2) ^ ((n/2 - 1)(n - n/2)) ≤ (M + 1) ^ godLabelled μ n        M = 9n (htm), 6n (qtm)
```

which gives the limit constant `log₂(24!/2)/4 ≈ 19.509` per `n²/log₂ n`. There is no `6⁶` factor: the goal
is one position.
-/

open Equiv

namespace RubiksGN

open Classical

variable {n : ℕ}

/-- The number of even permutations of the 24 coordinates of an orbit. -/
def evenN : ℕ := Nat.factorial 24 / 2

theorem evenN_mul : evenN * 2 = Nat.factorial 24 := by decide +kernel

/-- There are `24!/2` even permutations. -/
theorem card_alt : Fintype.card (alternatingGroup (Fin 24)) = evenN := by
  have h := two_mul_card_alternatingGroup (α := Fin 24)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  have h2 := evenN_mul
  convert (by omega : Fintype.card (alternatingGroup (Fin 24)) = evenN)

/-- The number of orbits `rows × cols`, wing orbits included. -/
def fullOrbits (n : ℕ) : ℕ := (n / 2 - 1) * (n - n / 2)

/-- The orbits `rows × cols`, as a type. -/
abbrev Full (n : ℕ) := {p : Fin n × Fin n // p ∈ rowsF n ×ˢ colsF n}

theorem card_Full : Fintype.card (Full n) = fullOrbits n := by
  rw [Fintype.card_coe, Finset.card_product, card_rowsF, card_colsF]
  rfl

theorem innerOrbits_le_fullOrbits : innerOrbits n ≤ fullOrbits n :=
  Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Any choice of even permutations on the orbits is realised by an element of the cube group. -/
theorem realiseL (hn : 2 ≤ n) (F : Full n → alternatingGroup (Fin 24)) :
    ∃ g ∈ cubeGroup n, ∀ (p : Full n) (k : Fin 24),
      g (e (rep p.1.1 p.1.2) k) = e (rep p.1.1 p.1.2) ((F p).1 k) := by
  have hR : ∀ i ∈ rowsF n, IsRow i := fun i hi => (Finset.mem_filter.1 hi).2
  have hC : ∀ j ∈ colsF n, IsCol j := fun j hj => (Finset.mem_filter.1 hj).2
  have hσ : ∀ i j : Fin n, ∃ S : List Letter, S.Sublist uSeq ∧
      ∀ hp : (i, j) ∈ rowsF n ×ˢ colsF n, prodL S = (F ⟨(i, j), hp⟩).1 := by
    intro i j
    by_cases hp : (i, j) ∈ rowsF n ×ˢ colsF n
    · obtain ⟨S, hS, hprod⟩ := universal (F ⟨(i, j), hp⟩).1
        (Equiv.Perm.mem_alternatingGroup.1 (F ⟨(i, j), hp⟩).2)
      exact ⟨S, hS, fun _ => hprod⟩
    · exact ⟨[], List.nil_sublist _, fun h => absurd h hp⟩
  choose S hS1 hS2 using hσ
  obtain ⟨W, _, _, _, hW⟩ := parallel_seq hn hR hC 1 one_pos uSeq S (fun i _ j _ => hS1 i j)
  refine ⟨Word.eval W, eval_mem W, ?_⟩
  rintro ⟨⟨i, j⟩, hp⟩ k
  have hp' := Finset.mem_product.1 hp
  rw [hW i hp'.1 j hp'.2, hS2 i j hp]

/-- The element realising a choice of permutations determines that choice. -/
theorem realiseL_inj {F F' : Full n → alternatingGroup (Fin 24)} {g : Perm (Sticker n)}
    (h : ∀ (p : Full n) (k : Fin 24),
      g (e (rep p.1.1 p.1.2) k) = e (rep p.1.1 p.1.2) ((F p).1 k))
    (h' : ∀ (p : Full n) (k : Fin 24),
      g (e (rep p.1.1 p.1.2) k) = e (rep p.1.1 p.1.2) ((F' p).1 k)) : F = F' := by
  funext p
  apply Subtype.ext
  ext k
  obtain ⟨⟨i, j⟩, hp⟩ := p
  have hp' := Finset.mem_product.1 hp
  have hd : InDom i j :=
    row_col_dom i j (Finset.mem_filter.1 hp'.1).2 (Finset.mem_filter.1 hp'.2).2
  have := (h ⟨(i, j), hp⟩ k).symm.trans (h' ⟨(i, j), hp⟩ k)
  have h3 := rep_e_inj i j i j _ _ hd hd this
  exact congrArg Fin.val h3.2.2

/-- The number of moves of a metric. -/
def moveCount (μ : Metric) (n : ℕ) : ℕ :=
  match μ with
  | .htm => 9 * n
  | .qtm => 6 * n

/-- The allowed moves, and "no move". -/
noncomputable def optMoves (μ : Metric) (n : ℕ) : Finset (Option (Move n)) :=
  (Finset.univ.filter fun m : Move n => μ.allows m).insertNone

theorem card_turn_filter :
    (Finset.univ.filter fun t : Turn => t ≠ .half).card = 2 := by
  have : (Finset.univ.filter fun t : Turn => t ≠ .half) = {.cw, .ccw} := by
    ext t
    cases t <;> simp
  rw [this]
  rfl

theorem card_allowed (μ : Metric) :
    (Finset.univ.filter fun m : Move n => μ.allows m).card = moveCount μ n := by
  cases μ with
  | htm =>
    have : (Finset.univ.filter fun m : Move n => Metric.htm.allows m) = Finset.univ :=
      Finset.filter_true_of_mem fun _ _ => trivial
    rw [this, Finset.card_univ, card_move]
    rfl
  | qtm =>
    have : (Finset.univ.filter fun m : Move n => Metric.qtm.allows m) =
        (Finset.univ : Finset Axis) ×ˢ ((Finset.univ : Finset (Fin n)) ×ˢ
          (Finset.univ.filter fun t : Turn => t ≠ .half)) := by
      ext ⟨a, i, t⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_filter]
      simp only [Metric.allows, Finset.mem_univ, true_and]
    rw [this, Finset.card_product, Finset.card_product, card_turn_filter, Finset.card_univ,
      Finset.card_univ, Fintype.card_fin]
    have h3 : Fintype.card Axis = 3 := rfl
    rw [h3]
    simp only [moveCount]
    ring

theorem card_optMoves (μ : Metric) : (optMoves μ n).card = moveCount μ n + 1 := by
  rw [optMoves, Finset.card_insertNone, card_allowed]

theorem padW_mem (μ : Metric) (K : ℕ) (w : Word n) (h : ∀ m ∈ w, μ.allows m) :
    padW K w ∈ Fintype.piFinset fun _ : Fin K => optMoves μ n := by
  rw [Fintype.mem_piFinset]
  intro t
  simp only [padW, optMoves, Finset.mem_insertNone]
  intro m hm
  simp only [Option.mem_def] at hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h m (List.mem_of_getElem? hm)

/-- **The counting bound for the labelled cube.** -/
theorem count_labelled (hn : 2 ≤ n) (μ : Metric) (K : ℕ) (hK : LabelledSolvable μ n K) :
    evenN ^ fullOrbits n ≤ (moveCount μ n + 1) ^ K := by
  choose g hg1 hg2 using realiseL (n := n) hn
  have hsol := fun F : Full n → alternatingGroup (Fin 24) => hK (g F) (hg1 F)
  choose w hw1 hw2 hw3 using hsol
  have hinj : ∀ F F', padW K (w F) = padW K (w F') → F = F' := by
    intro F F' h
    have h2 : w F = w F' := padW_inj K _ _ (hw2 F) (hw2 F') h
    have hg : g F = g F' := by
      have a := hw3 F
      have b := hw3 F'
      rw [h2] at a
      exact mul_left_cancel (a.trans b.symm)
    apply realiseL_inj (g := g F) (hg2 F)
    rw [hg]
    exact hg2 F'
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := Fintype.piFinset fun _ : Fin K => optMoves μ n) (fun F => padW K (w F))
    (fun F _ => padW_mem μ K (w F) (hw1 F)) (fun F _ F' _ h => hinj F F' h)
  rw [Fintype.card_piFinset_const, card_optMoves, Finset.card_univ,
    Fintype.card_fun, card_alt, card_Full] at hcard
  exact hcard

/-- **Labelled lower bound, exact form, all orbits and the true number of moves.** -/
theorem lowerLabelled_count_full (μ : Metric) (hn : 3 ≤ n) :
    (Nat.factorial 24 / 2) ^ fullOrbits n ≤ (moveCount μ n + 1) ^ godLabelled μ n :=
  count_labelled (by omega) μ _ (labelled_spec μ hn)

theorem moveCount_le (μ : Metric) (n : ℕ) : moveCount μ n ≤ 9 * n := by
  cases μ <;> simp only [moveCount] <;> omega

/-- **Labelled lower bound, exact form.** -/
theorem lowerLabelled_count (μ : Metric) (hn : 3 ≤ n) :
    (Nat.factorial 24 / 2) ^ innerOrbits n ≤ (9 * n + 1) ^ godLabelled μ n := by
  calc (Nat.factorial 24 / 2) ^ innerOrbits n
      ≤ (Nat.factorial 24 / 2) ^ fullOrbits n :=
        Nat.pow_le_pow_right (by decide +kernel) innerOrbits_le_fullOrbits
    _ ≤ (moveCount μ n + 1) ^ godLabelled μ n := lowerLabelled_count_full μ hn
    _ ≤ (9 * n + 1) ^ godLabelled μ n :=
        Nat.pow_le_pow_left (by have := moveCount_le μ n; omega) _

/-! ### Logarithmic forms -/

/-- `log₂ (24!/2)`. -/
noncomputable def LE : ℝ := lg (evenN : ℝ)

theorem pow_lower_evenN : 2 ^ 78037 ≤ evenN ^ 1000 := by decide +kernel

/-- `log₂ (24!/2) ≥ 78.037`. (It is `78.03766…`, so `78.04` would be false.) -/
theorem LE_lower : (78.037 : ℝ) ≤ LE := by
  have h : ((2 : ℝ) ^ 78037) ≤ (evenN : ℝ) ^ 1000 := by exact_mod_cast pow_lower_evenN
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  simp only [LE]
  push_cast at h2
  linarith

theorem fullOrbits_lower (hn : 3 ≤ n) :
    ((n : ℝ) + 1) * ((n : ℝ) - 3) / 4 ≤ (fullOrbits n : ℝ) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : 2 * (m + 1) / 2 - 1 = m := by omega
    have h2 : 2 * (m + 1) - 2 * (m + 1) / 2 = m + 1 := by omega
    simp only [fullOrbits, h1, h2]
    push_cast
    nlinarith
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : (2 * (m + 1) + 1) / 2 - 1 = m := by omega
    have h2 : 2 * (m + 1) + 1 - (2 * (m + 1) + 1) / 2 = m + 2 := by omega
    simp only [fullOrbits, h1, h2]
    push_cast
    nlinarith

/-- The labelled counting inequality with the exact logarithm of the number of moves. -/
theorem log_countL (μ : Metric) (hn : 3 ≤ n) :
    (fullOrbits n : ℝ) * LE ≤ (godLabelled μ n : ℝ) * lg (moveCount μ n + 1) := by
  have h := lowerLabelled_count_full μ hn
  have h' : (evenN : ℝ) ^ fullOrbits n ≤ ((moveCount μ n : ℝ) + 1) ^ godLabelled μ n := by
    exact_mod_cast h
  have hE : (0 : ℝ) < evenN := by
    have : 0 < evenN := by decide +kernel
    exact_mod_cast this
  have h2 := lg_mono (by positivity) h'
  rw [lg_pow, lg_pow] at h2
  simpa only [LE] using h2

theorem lg_moves_le (μ : Metric) (hn : 3 ≤ n) : lg (moveCount μ n + 1) ≤ lg n + 3.33 := by
  have hn0 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (moveCount μ n : ℝ) ≤ 9 * n := by exact_mod_cast moveCount_le μ n
  have hle : (moveCount μ n + 1 : ℝ) ≤ 10 * n := by linarith
  have := lg_mono (by positivity) hle
  rw [lg_mul (by norm_num) (by positivity)] at this
  linarith [lg10_upper]

/-- **The labelled lower constant in the limit.** -/
theorem lowerLabelled_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
      (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 - ε) * (n : ℝ) ^ 2 / Real.logb 2 n ≤
        godLabelled μ n := by
  change ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
    (LE / 4 - ε) * (n : ℝ) ^ 2 / lg n ≤ godLabelled μ n
  by_cases hc : LE / 4 - ε ≤ 0
  · refine ⟨2, fun n hn μ => ?_⟩
    have hx : 0 < lg n := by
      apply Real.logb_pos (by norm_num)
      exact_mod_cast (by omega : 1 < n)
    have : (LE / 4 - ε) * (n : ℝ) ^ 2 / lg n ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc (by positivity)) hx.le
    exact this.trans (by positivity)
  · rw [not_le] at hc
    set c := LE / 4 - ε with hcdef
    have hLpos : (0 : ℝ) < LE := by linarith [LE_lower]
    have htend : Filter.Tendsto (fun x : ℝ => lg x) Filter.atTop Filter.atTop :=
      Real.tendsto_logb_atTop (by norm_num)
    obtain ⟨X, hX⟩ := (Filter.tendsto_atTop.1 htend (3.33 * c / (ε / 2) + 1))
      |> Filter.eventually_atTop.1
    obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 / ε * LE)
    obtain ⟨N₂, hN₂⟩ := exists_nat_ge X
    refine ⟨max (max N₁ N₂) 3, fun n hn μ => ?_⟩
    have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : (N₁ : ℝ) ≤ n := by
      exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn2 : (N₂ : ℝ) ≤ n := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hNr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hxl := hX n (hN₂.trans hn2)
    have hratio : 3.33 * c / (ε / 2) ≥ 0 := by positivity
    have hx0 : 0 < lg n := by linarith
    have hxc : 3.33 * c ≤ (lg n) * (ε / 2) := by
      have : 3.33 * c / (ε / 2) ≤ lg n := by linarith
      rwa [div_le_iff₀ (by linarith)] at this
    have hG : (0 : ℝ) ≤ godLabelled μ n := by positivity
    have hlc : (fullOrbits n : ℝ) * LE ≤ (godLabelled μ n : ℝ) * (lg n + 3.33) :=
      (log_countL μ hn3).trans (mul_le_mul_of_nonneg_left (lg_moves_le μ hn3) hG)
    have hin := fullOrbits_lower hn3
    have h1 : LE * (((n : ℝ) + 1) * ((n : ℝ) - 3) / 4) ≤ (fullOrbits n : ℝ) * LE := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hin hLpos.le
    have hnε : LE ≤ ε / 2 * n := by
      have := hN₁.trans hn1
      have h2 : 2 / ε * LE * (ε / 2) = LE := by field_simp
      nlinarith
    have h2 : (c + ε / 2) * (n : ℝ) ^ 2 ≤ (godLabelled μ n : ℝ) * (lg n + 3.33) := by
      have h3 : (c + ε / 2) = LE / 4 - ε / 2 := by rw [hcdef]; ring
      rw [h3]
      have h4 : LE * n ≤ ε / 2 * n * n :=
        mul_le_mul_of_nonneg_right hnε (by positivity)
      have h5 : LE * (2 * n + 3) ≤ LE * (4 * n) :=
        mul_le_mul_of_nonneg_left (by linarith) hLpos.le
      nlinarith
    rw [div_le_iff₀ hx0]
    have hc' : c * (lg n + 3.33) ≤ (c + ε / 2) * lg n := by nlinarith
    have hprod : (c + ε / 2) * (n : ℝ) ^ 2 * lg n ≤
        (godLabelled μ n : ℝ) * (lg n + 3.33) * lg n :=
      mul_le_mul_of_nonneg_right h2 hx0.le
    have hsum : 0 < lg n + 3.33 := by linarith
    have hkey : c * (n : ℝ) ^ 2 * (lg n + 3.33) ≤ (godLabelled μ n : ℝ) * lg n * (lg n + 3.33) := by
      have : c * (n : ℝ) ^ 2 * (lg n + 3.33) ≤ (c + ε / 2) * (n : ℝ) ^ 2 * lg n := by
        have := mul_le_mul_of_nonneg_right hc' (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right hkey hsum

/-- `log₂ (24!/2) / 4 ≥ 19.509`. -/
theorem lgE_div_four : (19.509 : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 := by
  have := LE_lower
  simp only [LE, lg, evenN] at this
  linarith

/-- **The labelled lower bound with explicit lower-order terms.** -/
theorem lowerLabelled_second_order (μ : Metric) (hn : 100 ≤ n) :
    19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) / (lg n + 3.18) ≤ godLabelled μ n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < lg n := Real.logb_pos (by norm_num) (by linarith)
  have hc := log_countL μ (by omega : 3 ≤ n)
  have hin := fullOrbits_lower (by omega : 3 ≤ n)
  have hL := LE_lower
  have hI0 : (0 : ℝ) ≤ fullOrbits n := by positivity
  have h9 : lg (moveCount μ n + 1) ≤ lg n + 3.18 := by
    have hm : (moveCount μ n : ℝ) ≤ 9 * n := by exact_mod_cast moveCount_le μ n
    have hle : (moveCount μ n + 1 : ℝ) ≤ (901 / 100) * n := by linarith
    have := lg_mono (by positivity) hle
    rw [lg_mul (by norm_num) (by positivity)] at this
    linarith [lg901_upper]
  have hG : (0 : ℝ) ≤ godLabelled μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left h9 hG
  have h2 : (78.036 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) - 3) / 4) ≤ (fullOrbits n : ℝ) * LE := by
    calc (78.036 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) - 3) / 4) ≤ 78.036 * (fullOrbits n : ℝ) :=
          mul_le_mul_of_nonneg_left hin (by norm_num)
      _ ≤ LE * (fullOrbits n : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hI0
      _ = _ := mul_comm _ _
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The form with `(n-1)(n-3)`, for direct comparison with `lower_second_order`. -/
theorem lowerLabelled_second_order' (μ : Metric) (hn : 100 ≤ n) :
    19.509 * ((n : ℝ) - 1) * ((n : ℝ) - 3) / (lg n + 3.18) ≤ godLabelled μ n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < lg n := Real.logb_pos (by norm_num) (by linarith)
  refine le_trans ?_ (lowerLabelled_second_order μ hn)
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

/-- `log₂ 100 ≥ 6.64`. -/
theorem lg_ge_664 (hn : 100 ≤ n) : (6.64 : ℝ) ≤ lg n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have h : ((2 : ℝ) ^ 664) ≤ (100 : ℝ) ^ 100 := by
    exact_mod_cast (by decide +kernel : 2 ^ 664 ≤ 100 ^ 100)
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  have h3 := lg_mono (by norm_num) hN
  push_cast at h2
  linarith

/-- **Explicit labelled lower bound.** -/
theorem lowerLabelled_explicit (μ : Metric) (hn : 100 ≤ n) :
    12.9 * (n : ℝ) ^ 2 / lg n ≤ godLabelled μ n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := lg_ge_664 hn
  have hx0 : 0 < lg n := by linarith
  have h := lowerLabelled_second_order μ hn
  rw [div_le_iff₀ (by linarith)] at h
  have hG : (0 : ℝ) ≤ godLabelled μ n := by positivity
  rw [div_le_iff₀ hx0]
  -- `19.509 (n² - 2n - 3) ≥ 19.11 n²` and `lg n / (lg n + 3.18) ≥ 0.675`.
  have h1 : (19.11 : ℝ) * (n : ℝ) ^ 2 ≤ 19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) := by nlinarith
  have h2 : (19.11 : ℝ) * (n : ℝ) ^ 2 ≤ (godLabelled μ n : ℝ) * (lg n + 3.18) := h1.trans h
  have h3 : (lg n + 3.18) * 12.9 ≤ 19.11 * lg n := by linarith
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h4 := mul_le_mul_of_nonneg_right h3 hn2
  have h5 := mul_le_mul_of_nonneg_right h2 hx0.le
  have hsum : 0 < lg n + 3.18 := by linarith
  have key : (12.9 * (n : ℝ) ^ 2) * (lg n + 3.18) ≤ ((godLabelled μ n : ℝ) * lg n) * (lg n + 3.18) := by
    nlinarith
  exact le_of_mul_le_mul_right key hsum

end RubiksGN
