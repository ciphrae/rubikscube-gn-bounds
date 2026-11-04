import Mathlib
import RubiksGN.TrieCost
import RubiksGN.ExactLimit

/-!
# The second-order term of the round scheme with trie slots

For `x = ⌊log₂ n⌋`, `S = 2 x⁴`. A list of key `k = (m, w)` has a parameter `y` and `s = ⌊log_m (n / (x y))⌋`, so that
`T = m^s` satisfies `n / (x T) ∈ [y, m y]`. Then, with `D = log₂ n - log₂ x` (the theorem `trieExactW_le`),

`trieExactW ≤ base + (n²/8) (1 + 1/x³) Σ_k log₂ m_k / (D - c_k)`,

as soon as `log₂ y + R/y ≤ c_k` and `log₂ (m y) + R/(m y) ≤ c_k`, with `R = (1 + ε) · 8 w / (m - 1)`: the function `log₂ Y + R/Y` is
convex in `log₂ Y`, so it is below `c_k` on the whole interval (`convex_ends`). The averaging of the `c_k` over the lists is
`sum_div_le`.

This is the form with `c_k` in hundredths, checked by `keyOK` in integer arithmetic.
-/

open Real

namespace RubiksGN

/-- Base-2 logarithm. -/
local notation "lg₂" => Real.logb 2

/-! ### Convexity -/

/-- `log₂ Y + B / Y` is at most its maximum on the ends of an interval: it is convex in `log Y`. -/
theorem convex_ends {a b B c Y : ℝ} (ha : 0 < a) (hab : a ≤ b) (h1 : lg₂ a + B / a ≤ c)
    (h2 : lg₂ b + B / b ≤ c) (hB : 0 ≤ B) (hY : a ≤ Y) (hYb : Y ≤ b) : lg₂ Y + B / Y ≤ c := by
  have hb : 0 < b := by linarith
  have hY0 : 0 < Y := by linarith
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have : Y = a := le_antisymm hYb hY
    rw [this]
    exact h1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log a < Real.log b := Real.log_lt_log ha hlt
  have hl1 : Real.log a ≤ Real.log Y := Real.log_le_log ha hY
  have hl2 : Real.log Y ≤ Real.log b := Real.log_le_log hY0 hYb
  set t := (Real.log Y - Real.log a) / (Real.log b - Real.log a) with ht
  have hd : 0 < Real.log b - Real.log a := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hd]
    linarith
  have hly : Real.log Y = (1 - t) * Real.log a + t * Real.log b := by
    rw [ht]
    field_simp
    ring
  have hcv := convexOn_exp.2 (Set.mem_univ (-Real.log a)) (Set.mem_univ (-Real.log b))
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hcv
  have hexp : Real.exp ((1 - t) * -Real.log a + t * -Real.log b) = 1 / Y := by
    have : (1 - t) * -Real.log a + t * -Real.log b = -Real.log Y := by
      rw [hly]
      ring
    rw [this, Real.exp_neg, Real.exp_log hY0, one_div]
  have ea : Real.exp (-Real.log a) = 1 / a := by rw [Real.exp_neg, Real.exp_log ha, one_div]
  have eb : Real.exp (-Real.log b) = 1 / b := by rw [Real.exp_neg, Real.exp_log hb, one_div]
  rw [hexp, ea, eb] at hcv
  have hlg : lg₂ Y = (1 - t) * lg₂ a + t * lg₂ b := by
    simp only [Real.logb]
    rw [hly]
    ring
  have hmul := mul_le_mul_of_nonneg_left hcv hB
  have e1 : B * (1 / Y) = B / Y := by ring
  have e2 : B * ((1 - t) * (1 / a) + t * (1 / b)) = (1 - t) * (B / a) + t * (B / b) := by ring
  rw [e1, e2] at hmul
  rw [hlg]
  have s1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - t)
  have s2 := mul_le_mul_of_nonneg_left h2 ht0
  nlinarith

/-! ### One list -/

theorem geomS_le_real (m s : ℕ) (hm : 2 ≤ m) : (geomS m s : ℝ) ≤ (m : ℝ) ^ s / ((m : ℝ) - 1) := by
  have h := geomS_mul m s (by omega)
  have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hr : ((m : ℝ) - 1) * geomS m s + 1 = (m : ℝ) ^ s := by
    rw [← h1]
    exact_mod_cast h
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [le_div_iff₀ hm1]
  nlinarith

/-- The inequality behind the choice of `s`. `E = D - c`, `s log₂ m = D - log₂ Y`, `T = n / (x Y)`. -/
theorem rate_le {s lm E X Y R c D : ℝ} (hs : 0 < s) (hE : 0 < E) (hEX : E ≤ X) (hX : 0 < X) (hY : 0 < Y)
    (hR : 0 ≤ R) (hED : E = D - c) (hsl : s * lm = D - lg₂ Y) (hc : lg₂ Y + R / Y ≤ c) :
    (1 / s) * (1 + R / (X * Y)) ≤ lm / E := by
  have h1 : E * (R / (X * Y)) ≤ R / Y := by
    have e : R / Y = X * (R / (X * Y)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hEX (by positivity)
  have e0 : (1 + R / (X * Y)) * E = E + E * (R / (X * Y)) := by ring
  have h2 : (1 + R / (X * Y)) * E ≤ lm * s := by
    rw [e0, mul_comm lm s, hsl]
    linarith
  have e : (1 / s) * (1 + R / (X * Y)) = (1 + R / (X * Y)) / s := by ring
  rw [e, div_le_div_iff₀ hs hE]
  exact h2

/-- The hypotheses on one key, in real form. -/
structure KeyReal (m w y : ℕ) (c : ℝ) : Prop where
  hm : 2 ≤ m
  hy : 1 ≤ y
  h1 : lg₂ (y : ℝ) + ((8 * w / ((m : ℝ) - 1)) * (1001 / 1000)) / y ≤ c
  h2 : lg₂ ((m : ℝ) * y) + ((8 * w / ((m : ℝ) - 1)) * (1001 / 1000)) / ((m : ℝ) * y) ≤ c

/-- The real form of the pieces of one list: the number of chunks. -/
theorem piece_chunks (x s : ℕ) (hs : 0 < s) (hsx : s ≤ x) :
    ((2 * x ^ 4 / 2 / s + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ 4 / s * (1 + 1 / (x : ℝ) ^ 3) := by
  have hx : 0 < x := by omega
  have hX : (0 : ℝ) < x := by exact_mod_cast hx
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsX : (s : ℝ) ≤ x := by exact_mod_cast hsx
  have e : 2 * x ^ 4 / 2 = x ^ 4 := by omega
  rw [e]
  push_cast
  have a := Nat.cast_div_le (α := ℝ) (m := x ^ 4) (n := s)
  push_cast at a
  have b : (1 : ℝ) ≤ (x : ℝ) ^ 4 / s * (1 / (x : ℝ) ^ 3) := by
    have e2 : (x : ℝ) ^ 4 / s * (1 / (x : ℝ) ^ 3) = x / s := by
      field_simp
    rw [e2, le_div_iff₀ hsR]
    linarith
  have e3 : (x : ℝ) ^ 4 / s * (1 + 1 / (x : ℝ) ^ 3) = (x : ℝ) ^ 4 / s + (x : ℝ) ^ 4 / s * (1 / (x : ℝ) ^ 3) := by
    ring
  rw [e3]
  linarith

/-- The real form of the pieces of one list: the columns. -/
theorem piece_cols (n x r : ℕ) (hr : 2 * r ≤ n) (hx : 0 < x) :
    ((r ^ 2 / (2 * x ^ 4) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 4) ∧
      ((r / (2 * x ^ 4) : ℕ) : ℝ) + 1 ≤ (n : ℝ) / (4 * (x : ℝ) ^ 4) + 1 := by
  have hX : (0 : ℝ) < x := by exact_mod_cast hx
  have hr2 : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have h : (2 : ℝ) * r ≤ n := by exact_mod_cast hr
    linarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hS : (0 : ℝ) < 2 * (x : ℝ) ^ 4 := by positivity
  have hx4 : (0 : ℝ) < (x : ℝ) ^ 4 := by positivity
  constructor
  · have a := Nat.cast_div_le (α := ℝ) (m := r ^ 2) (n := 2 * x ^ 4)
    push_cast at a
    refine a.trans ?_
    rw [div_le_div_iff₀ hS (by positivity)]
    have hsq : (r : ℝ) ^ 2 ≤ ((n : ℝ) / 2) ^ 2 := by gcongr
    calc (r : ℝ) ^ 2 * (8 * (x : ℝ) ^ 4) ≤ ((n : ℝ) / 2) ^ 2 * (8 * (x : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = _ := by ring
  · have a := Nat.cast_div_le (α := ℝ) (m := r) (n := 2 * x ^ 4)
    push_cast at a
    have b : (r : ℝ) / (2 * (x : ℝ) ^ 4) ≤ (n : ℝ) / (4 * (x : ℝ) ^ 4) := by
      rw [div_le_div_iff₀ hS (by positivity)]
      calc (r : ℝ) * (4 * (x : ℝ) ^ 4) ≤ ((n : ℝ) / 2) * (4 * (x : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_right hr2 (by positivity)
        _ = _ := by ring
    linarith

/-- The bracket of one list. -/
theorem bracket_le {N X W m T Y R a b c : ℝ} (hN : 0 < N) (hX : 0 < X) (hW : 0 ≤ W) (hm : 0 < m - 1)
    (hT : 0 < T) (hY : 0 < Y) (hTY : T = N / (X * Y)) (hR : R = (8 * W / (m - 1)) * (1001 / 1000))
    (heps : 4 * X ^ 4 / N ≤ 1 / 1000) (ha : a ≤ N ^ 2 / (8 * X ^ 4))
    (hb : b ≤ N / (4 * X ^ 4) + 1) (hc : c ≤ 2 * W * (T / (m - 1))) (hc0 : 0 ≤ c) :
    a + 2 * b * c ≤ N ^ 2 / (8 * X ^ 4) * (1 + R / (X * Y)) := by
  have hx4 : 0 < X ^ 4 := by positivity
  have q1 : 2 * b * c ≤ 2 * (N / (4 * X ^ 4) + 1) * (2 * W * (T / (m - 1))) := by
    have h1 : 2 * b ≤ 2 * (N / (4 * X ^ 4) + 1) := by linarith
    exact mul_le_mul h1 hc hc0 (by positivity)
  have q2 : 2 * (N / (4 * X ^ 4) + 1) * (2 * W * (T / (m - 1))) =
      N ^ 2 / (8 * X ^ 4) * ((1 + 4 * X ^ 4 / N) * (8 * W / (m - 1) * (T / N))) := by
    field_simp
    ring
  have q3 : (1 + 4 * X ^ 4 / N) * (8 * W / (m - 1) * (T / N)) ≤ R / (X * Y) := by
    have e : R / (X * Y) = (1001 / 1000) * (8 * W / (m - 1) * (T / N)) := by
      have : T / N = 1 / (X * Y) := by
        rw [hTY]
        field_simp
      rw [this, hR]
      ring
    rw [e]
    have h0 : 0 ≤ 8 * W / (m - 1) * (T / N) := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) h0
  have q4 := mul_le_mul_of_nonneg_left q3 (by positivity : 0 ≤ N ^ 2 / (8 * X ^ 4))
  rw [mul_add, mul_one]
  linarith

/-- **The cost of one list.** `D = log₂ n - log₂ x`. -/
theorem list_term {m w y n x : ℕ} {c D : ℝ} (hk : KeyReal m w y c) (hx : 0 < x)
    (hxn : n < 2 ^ (x + 1)) (hmy : m * (x * y) ≤ n) (heps : 4000 * x ^ 4 ≤ n)
    (hD : D = lg₂ n - lg₂ x) (hE : 0 < D - c) (hEX : D - c ≤ x) :
    (((2 * x ^ 4 / 2 / Nat.log m (n / (x * y)) + 1 : ℕ) : ℝ) *
        ((((n / 2 - 1) ^ 2 / (2 * x ^ 4) : ℕ) : ℝ) +
          2 * ((((n / 2 - 1) / (2 * x ^ 4) : ℕ) : ℝ) + 1) *
            ((2 * w * geomS m (Nat.log m (n / (x * y))) : ℕ) : ℝ))) ≤
      (n : ℝ) ^ 2 / 8 * (1 + 1 / (x : ℝ) ^ 3) * (lg₂ (m : ℝ) / (D - c)) := by
  obtain ⟨hm, hy, h1, h2⟩ := hk
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.log m (n / (x * y)) := ⟨_, rfl⟩
  rw [← hs]
  have hxy : 0 < x * y := by positivity
  have hU : m ≤ n / (x * y) := by
    rw [Nat.le_div_iff_mul_le hxy]
    exact hmy
  have hU0 : n / (x * y) ≠ 0 := by omega
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Nat.log_pos (by omega) hU
  have hT1 : m ^ s ≤ n / (x * y) := by
    rw [hs]
    exact Nat.pow_log_le_self m hU0
  have hT2 : n / (x * y) < m ^ (s + 1) := by
    rw [hs]
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hsx : s ≤ x := by
    have a : 2 ^ s ≤ m ^ s := Nat.pow_le_pow_left hm s
    have b : n / (x * y) ≤ n := Nat.div_le_self _ _
    have c' : 2 ^ s < 2 ^ (x + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 c'
    omega
  have hn0 : 0 < n := by
    have : 0 < m * (x * y) := by positivity
    omega
  -- reals
  have hX : (0 : ℝ) < x := by exact_mod_cast hx
  have hN : (0 : ℝ) < n := by exact_mod_cast hn0
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs1
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (m : ℝ) ^ s := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = (n : ℝ) / (x * T) := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  have hTY : T = (n : ℝ) / (x * Y) := by
    rw [hYdef]
    field_simp
  -- `y ≤ Y ≤ m y`
  have hYlow : (y : ℝ) ≤ Y := by
    rw [hYdef, le_div_iff₀ (by positivity)]
    have a : m ^ s * (x * y) ≤ n := by
      calc m ^ s * (x * y) ≤ n / (x * y) * (x * y) := Nat.mul_le_mul_right _ hT1
        _ ≤ n := Nat.div_mul_le_self _ _
    have b : (T : ℝ) * ((x : ℝ) * y) ≤ n := by
      rw [hT]
      exact_mod_cast a
    calc (y : ℝ) * (x * T) = T * ((x : ℝ) * y) := by ring
      _ ≤ n := b
  have hYup : Y ≤ (m : ℝ) * y := by
    rw [hYdef, div_le_iff₀ (by positivity)]
    have a : n < (x * y) * (n / (x * y) + 1) := Nat.lt_mul_div_succ n hxy
    have b : n / (x * y) + 1 ≤ m ^ (s + 1) := hT2
    have c' : n ≤ (x * y) * m ^ (s + 1) := a.le.trans (Nat.mul_le_mul_left _ b)
    have d : (n : ℝ) ≤ ((x : ℝ) * y) * (m : ℝ) ^ (s + 1) := by exact_mod_cast c'
    have e : (m : ℝ) ^ (s + 1) = (m : ℝ) * T := by rw [hT, pow_succ]; ring
    rw [e] at d
    calc (n : ℝ) ≤ ((x : ℝ) * y) * ((m : ℝ) * T) := d
      _ = _ := by ring
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (8 * w / ((m : ℝ) - 1)) * (1001 / 1000) := ⟨_, rfl⟩
  rw [← hRdef] at h1 h2
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hYc : lg₂ Y + R / Y ≤ c := by
    refine convex_ends (a := (y : ℝ)) (b := (m : ℝ) * y) (by linarith) ?_ h1 h2 hR0 hYlow hYup
    exact le_mul_of_one_le_left (by linarith) (by linarith)
  -- `s log₂ m = D - log₂ Y`
  have hsl : (s : ℝ) * lg₂ (m : ℝ) = D - lg₂ Y := by
    have e1 : lg₂ T = (s : ℝ) * lg₂ (m : ℝ) := by rw [hT, Real.logb_pow]
    have e2 : lg₂ Y = lg₂ n - (lg₂ (x : ℝ) + lg₂ T) := by
      rw [hYdef, Real.logb_div hN.ne' (by positivity), Real.logb_mul hX.ne' hT0.ne']
    rw [hD, e2, e1]
    ring
  have hrate := rate_le (s := (s : ℝ)) (lm := lg₂ (m : ℝ)) (E := D - c) (X := (x : ℝ)) (Y := Y) (R := R)
    (c := c) (D := D) hsR hE hEX hX hY0 hR0 rfl hsl hYc
  -- the pieces
  have p1 := piece_chunks x s hs1 hsx
  obtain ⟨p2, p3⟩ := piece_cols n x (n / 2 - 1) (by omega) hx
  have p4 : ((2 * w * geomS m s : ℕ) : ℝ) ≤ 2 * w * (T / ((m : ℝ) - 1)) := by
    push_cast
    have := geomS_le_real m s hm
    rw [hT]
    gcongr
  have heps' : 4 * (x : ℝ) ^ 4 / n ≤ 1 / 1000 := by
    rw [div_le_iff₀ hN]
    have : (4000 : ℝ) * (x : ℝ) ^ 4 ≤ n := by exact_mod_cast heps
    linarith
  have hbr := bracket_le (W := (w : ℝ)) (m := (m : ℝ))
    (b := (((n / 2 - 1) / (2 * x ^ 4) : ℕ) : ℝ) + 1) hN hX (by positivity) hm1 hT0 hY0 hTY hRdef heps' p2
    p3 p4 (by positivity)
  have hbr0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 4) * (1 + R / (x * Y)) := by positivity
  have hp10 : 0 ≤ (x : ℝ) ^ 4 / s * (1 + 1 / (x : ℝ) ^ 3) := by positivity
  have hbr' : ((((n / 2 - 1) ^ 2 / (2 * x ^ 4) : ℕ) : ℝ) +
      2 * ((((n / 2 - 1) / (2 * x ^ 4) : ℕ) : ℝ) + 1) * ((2 * w * geomS m s : ℕ) : ℝ)) ≤
      (n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 4) * (1 + R / (x * Y)) := hbr
  calc _ ≤ ((x : ℝ) ^ 4 / s * (1 + 1 / (x : ℝ) ^ 3)) *
        ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 4) * (1 + R / (x * Y))) := mul_le_mul p1 hbr' (by positivity) hp10
    _ = (n : ℝ) ^ 2 / 8 * (1 + 1 / (x : ℝ) ^ 3) * ((1 / (s : ℝ)) * (1 + R / (x * Y))) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hrate (by positivity)

/-! ### All lists -/

/-- The word length as a sum over the lists. -/
theorem trieExactW_eq_sum (n S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) :
    trieExactW n S sOf ks = 3 * n + 406 + 2200 * ((n / 2 - 1) * (S + 2)) +
      (ks.map fun k => (S / 2 / sOf k + 1) * ((n / 2 - 1) ^ 2 / S +
        2 * ((n / 2 - 1) / S + 1) * (2 * k.2 * geomS k.1 (sOf k)))).sum := by
  simp only [trieExactW, trieRounds, trieSlots]
  rw [Nat.add_assoc]
  congr 1
  induction ks with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

/-- The chunk size of a key. -/
def sPar (yOf : ℕ × ℕ → ℕ) (n : ℕ) (k : ℕ × ℕ) : ℕ := Nat.log k.1 (n / (Nat.log 2 n * yOf k))

/-- **The word length with trie slots.** -/
theorem trieExactW_le (ks : List (ℕ × ℕ)) (yOf : ℕ × ℕ → ℕ) (cOf : ℕ × ℕ → ℝ)
    (hk : ∀ k ∈ ks, KeyReal k.1 k.2 (yOf k) (cOf k)) {n : ℕ}
    (hx : 0 < Nat.log 2 n) (hmy : ∀ k ∈ ks, k.1 * (Nat.log 2 n * yOf k) ≤ n)
    (heps : 4000 * (Nat.log 2 n) ^ 4 ≤ n)
    (hE : ∀ k ∈ ks, 0 < lg₂ n - lg₂ (Nat.log 2 n : ℕ) - cOf k)
    (hEX : ∀ k ∈ ks, lg₂ n - lg₂ (Nat.log 2 n : ℕ) - cOf k ≤ (Nat.log 2 n : ℕ)) :
    (trieExactW n (2 * (Nat.log 2 n) ^ 4) (sPar yOf n) ks : ℝ) ≤
      ((3 * n + 406 + 2200 * ((n / 2 - 1) * (2 * (Nat.log 2 n) ^ 4 + 2)) : ℕ) : ℝ) +
        (n : ℝ) ^ 2 / 8 * (1 + 1 / ((Nat.log 2 n : ℕ) : ℝ) ^ 3) *
          (ks.map fun k => lg₂ (k.1 : ℝ) / (lg₂ n - lg₂ (Nat.log 2 n : ℕ) - cOf k)).sum := by
  rw [trieExactW_eq_sum]
  obtain ⟨x, hxdef⟩ : ∃ x, x = Nat.log 2 n := ⟨_, rfl⟩
  rw [← hxdef] at hx hmy heps hE hEX ⊢
  have hlt : n < 2 ^ (x + 1) := by
    rw [hxdef]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  have key : ∀ ks' : List (ℕ × ℕ), (∀ k ∈ ks', k ∈ ks) →
      (((ks'.map fun k => (2 * x ^ 4 / 2 / sPar yOf n k + 1) * ((n / 2 - 1) ^ 2 / (2 * x ^ 4) +
        2 * ((n / 2 - 1) / (2 * x ^ 4) + 1) * (2 * k.2 * geomS k.1 (sPar yOf n k)))).sum : ℕ) : ℝ) ≤
        (n : ℝ) ^ 2 / 8 * (1 + 1 / ((x : ℕ) : ℝ) ^ 3) *
          (ks'.map fun k => lg₂ (k.1 : ℝ) / (lg₂ n - lg₂ (x : ℕ) - cOf k)).sum := by
    intro ks' hsub
    induction ks' with
    | nil => simp
    | cons a t ih =>
      have ih' := ih fun k hk' => hsub k (List.mem_cons_of_mem _ hk')
      have ha := hsub a List.mem_cons_self
      have hterm := list_term (hk a ha) hx hlt (hmy a ha) heps rfl (hE a ha) (hEX a ha)
      simp only [List.map_cons, List.sum_cons]
      refine (le_of_eq (Nat.cast_add _ _)).trans
        ((add_le_add ?_ ih').trans (le_of_eq (mul_add _ _ _).symm))
      refine le_trans (le_of_eq ?_) hterm
      simp only [sPar, ← hxdef]
      push_cast
      ring
  have h := key ks fun _ h => h
  rw [Nat.cast_add]
  exact add_le_add le_rfl h

/-! ### The conditions on a key, in integers -/

/-- The conditions of a key `k = (m, w)` for a parameter `y` and a constant `c` in hundredths. -/
def keyOK (y c : ℕ) (k : ℕ × ℕ) : Prop :=
  2 ≤ k.1 ∧ 1 ≤ y ∧
    (8 * k.2 * 1001) / (10 * (k.1 - 1) * y) + 1 ≤ c ∧
    (8 * k.2 * 1001) / (10 * (k.1 - 1) * (k.1 * y)) + 1 ≤ c ∧
    y ^ 100 ≤ 2 ^ (c - ((8 * k.2 * 1001) / (10 * (k.1 - 1) * y) + 1)) ∧
    (k.1 * y) ^ 100 ≤ 2 ^ (c - ((8 * k.2 * 1001) / (10 * (k.1 - 1) * (k.1 * y)) + 1))

instance (y c : ℕ) (k : ℕ × ℕ) : Decidable (keyOK y c k) := by
  unfold keyOK
  infer_instance

/-- One end of the interval. -/
theorem key_end (m w Y c : ℕ) (hm : 2 ≤ m) (hY : 1 ≤ Y)
    (he : (8 * w * 1001) / (10 * (m - 1) * Y) + 1 ≤ c)
    (hp : Y ^ 100 ≤ 2 ^ (c - ((8 * w * 1001) / (10 * (m - 1) * Y) + 1))) :
    lg₂ (Y : ℝ) + ((8 * w / ((m : ℝ) - 1)) * (1001 / 1000)) / Y ≤ (c : ℝ) / 100 := by
  obtain ⟨e, hedef⟩ : ∃ e, e = (8 * w * 1001) / (10 * (m - 1) * Y) + 1 := ⟨_, rfl⟩
  rw [← hedef] at he hp
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hm1R : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hB : 0 < 10 * (m - 1) * Y := by
    have : 0 < m - 1 := by omega
    positivity
  -- the logarithm
  have h1 : (100 : ℝ) * lg₂ (Y : ℝ) ≤ (c : ℝ) - e := by
    have hr : ((Y : ℝ)) ^ 100 ≤ (2 : ℝ) ^ (c - e) := by exact_mod_cast hp
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hr
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    rw [Nat.cast_sub he] at h2
    push_cast at h2
    linarith
  -- the fraction
  have h3 : ((8 * w / ((m : ℝ) - 1)) * (1001 / 1000)) / Y ≤ (e : ℝ) / 100 := by
    have a : (8 * w * 1001 : ℕ) < (10 * (m - 1) * Y) * ((8 * w * 1001) / (10 * (m - 1) * Y) + 1) :=
      Nat.lt_mul_div_succ _ hB
    rw [← hedef] at a
    have b : (8 * (w : ℝ) * 1001) ≤ 10 * ((m : ℝ) - 1) * Y * e := by
      rw [← hm1R]
      exact_mod_cast a.le
    have e1 : ((8 * w / ((m : ℝ) - 1)) * (1001 / 1000)) / Y =
        (8 * (w : ℝ) * 1001) / (1000 * ((m : ℝ) - 1) * Y) := by
      field_simp
    rw [e1, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h4 : (c : ℝ) / 100 = lg₂ (Y : ℝ) + ((c : ℝ) - 100 * lg₂ (Y : ℝ)) / 100 := by ring
  rw [h4]
  have h5 : (e : ℝ) / 100 ≤ ((c : ℝ) - 100 * lg₂ (Y : ℝ)) / 100 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  linarith

theorem keyReal_of_ok {y c : ℕ} {k : ℕ × ℕ} (h : keyOK y c k) :
    KeyReal k.1 k.2 y ((c : ℝ) / 100) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, key_end _ _ _ _ h1 h2 h3 h5, ?_⟩
  have := key_end k.1 k.2 (k.1 * y) c h1 (by nlinarith) h4 h6
  push_cast at this
  exact this

/-! ### Averaging over the lists -/

/-- `Σ a / (E - e)`, by the second-order expansion at `e = 0`. -/
theorem sum_div_le {κ : Type*} (ks : List κ) (a e : κ → ℝ) (E h : ℝ) (hE : h < E) (hh : 0 ≤ h)
    (ha : ∀ k ∈ ks, 0 ≤ a k) (he : ∀ k ∈ ks, |e k| ≤ h) :
    (ks.map fun k => a k / (E - e k)).sum ≤
      (ks.map a).sum * (1 / E + h ^ 2 / (E ^ 2 * (E - h))) + (ks.map fun k => a k * e k).sum * (1 / E ^ 2) := by
  have hE0 : 0 < E := by linarith
  have hEh : 0 < E - h := by linarith
  induction ks with
  | nil => simp
  | cons x t ih =>
    have ih' := ih (fun k hk => ha k (List.mem_cons_of_mem _ hk)) (fun k hk => he k (List.mem_cons_of_mem _ hk))
    simp only [List.map_cons, List.sum_cons]
    have hax := ha x List.mem_cons_self
    obtain ⟨hl, hu⟩ := abs_le.1 (he x List.mem_cons_self)
    obtain ⟨z, hz⟩ : ∃ z, z = e x := ⟨_, rfl⟩
    rw [← hz] at hl hu ⊢
    have hEz : 0 < E - z := by linarith
    have hEz' : E - h ≤ E - z := by linarith
    have hzsq : z ^ 2 ≤ h ^ 2 := by nlinarith
    have key : 1 / (E - z) ≤ 1 / E + h ^ 2 / (E ^ 2 * (E - h)) + z * (1 / E ^ 2) := by
      have e1 : 1 / (E - z) = 1 / E + z * (1 / E ^ 2) + z ^ 2 / (E ^ 2 * (E - z)) := by
        field_simp
        ring
      have e2 : z ^ 2 / (E ^ 2 * (E - z)) ≤ h ^ 2 / (E ^ 2 * (E - h)) := by
        apply div_le_div₀ (by positivity) hzsq (by positivity)
        exact mul_le_mul_of_nonneg_left hEz' (by positivity)
      rw [e1]
      linarith
    have hmul := mul_le_mul_of_nonneg_left key hax
    have e3 : a x / (E - z) = a x * (1 / (E - z)) := by ring
    rw [e3]
    calc a x * (1 / (E - z)) + _ ≤ a x * (1 / E + h ^ 2 / (E ^ 2 * (E - h)) + z * (1 / E ^ 2)) + _ :=
          add_le_add hmul ih'
      _ = _ := by ring

/-- The weighted sum of the constants, as a product. -/
theorem sum_mul_logb (ks : List (ℕ × ℕ)) (cOf : ℕ × ℕ → ℕ) (hm : ∀ k ∈ ks, 0 < k.1) :
    (ks.map fun k => (cOf k : ℝ) * lg₂ (k.1 : ℝ)).sum =
      lg₂ (((ks.map fun k => k.1 ^ cOf k).prod : ℕ) : ℝ) := by
  induction ks with
  | nil => simp
  | cons a t ih =>
    have ha := hm a List.mem_cons_self
    have ht : ∀ k ∈ t, 0 < k.1 := fun k hk => hm k (List.mem_cons_of_mem _ hk)
    have hp : 0 < (t.map fun k => k.1 ^ cOf k).prod := List.prod_pos fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact pow_pos (ht k hk) _
    simp only [List.map_cons, List.sum_cons, List.prod_cons, ih ht]
    rw [Nat.cast_mul, Real.logb_mul (by positivity) (by exact_mod_cast hp.ne'), Nat.cast_pow, Real.logb_pow]

/-- The weighted average of the constants is at most `c₀`. -/
theorem weighted_le (ks : List (ℕ × ℕ)) (cOf : ℕ × ℕ → ℕ) (c₀ : ℕ) (hm : ∀ k ∈ ks, 0 < k.1)
    (hp : (ks.map fun k => k.1 ^ cOf k).prod ≤ (ks.map fun k => k.1 ^ c₀).prod) :
    (ks.map fun k => lg₂ (k.1 : ℝ) * ((cOf k : ℝ) / 100 - (c₀ : ℝ) / 100)).sum ≤ 0 := by
  have e : ∀ l : List (ℕ × ℕ), (l.map fun k => lg₂ (k.1 : ℝ) * ((cOf k : ℝ) / 100 - (c₀ : ℝ) / 100)).sum =
      ((l.map fun k => (cOf k : ℝ) * lg₂ (k.1 : ℝ)).sum -
        (l.map fun k => (((fun _ : ℕ × ℕ => c₀) k : ℕ) : ℝ) * lg₂ (k.1 : ℝ)).sum) / 100 := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  rw [e, sum_mul_logb ks cOf hm, sum_mul_logb ks (fun _ => c₀) hm]
  have hpos : 0 < (ks.map fun k => k.1 ^ cOf k).prod := List.prod_pos fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact pow_pos (hm k hk) _
  have hr : (((ks.map fun k => k.1 ^ cOf k).prod : ℕ) : ℝ) ≤ (((ks.map fun k => k.1 ^ c₀).prod : ℕ) : ℝ) := by
    exact_mod_cast hp
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hpos) hr
  apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
  linarith

/-! ### The closed form -/

/-- `log₂ y ≤ y - 58` for `y ≥ 64`. -/
theorem lg_le_sub {y : ℝ} (hy : 64 ≤ y) : lg₂ y ≤ y - 58 := by
  have h64 : lg₂ 64 = 6 := by
    have : (64 : ℝ) = 2 ^ 6 := by norm_num
    rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hy0 : 0 < y := by linarith
  have hsplit : lg₂ y = lg₂ 64 + lg₂ (y / 64) := by
    rw [← Real.logb_mul (by norm_num) (by positivity)]
    congr 1
    ring
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hq : 0 < y / 64 := by positivity
  have h1 : Real.log (y / 64) ≤ y / 64 - 1 := Real.log_le_sub_one_of_pos hq
  have hq1 : 0 ≤ y / 64 - 1 := by
    have : 1 ≤ y / 64 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  have h2 : lg₂ (y / 64) ≤ (y / 64 - 1) / 0.69 := by
    rw [Real.logb, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  rw [hsplit, h64]
  have h3 : (y / 64 - 1) / 0.69 ≤ y - 64 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

theorem poly_le_two_pow_trie (x : ℕ) (hx : 64 ≤ x) : 2 ^ 17 * x ^ 6 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [pow_succ 2 x]
    refine le_trans ?_ (Nat.mul_le_mul_right 2 ih)
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hx
    ring_nf
    nlinarith [Nat.zero_le y, Nat.zero_le (y ^ 2), Nat.zero_le (y ^ 3), Nat.zero_le (y ^ 4), Nat.zero_le (y ^ 5),
      Nat.zero_le (y ^ 6)]

/-- The numeric step: with `u = 1 / E`. -/
theorem final_numeric {E X : ℝ} (hE : 50 ≤ E) (hEX : E ≤ X) (hX : 64 ≤ X) :
    (1 + 1 / X ^ 3) * (1 / E + 0.9 ^ 2 / (E ^ 2 * (E - 0.9))) + 0.001 / E ^ 2 ≤ 1 / (E - 0.02) := by
  have hE0 : 0 < E := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = 1 / E := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 50 := by
    rw [hu]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hEu : E * u = 1 := by rw [hu]; field_simp
  have a : 1 / X ^ 3 ≤ u / 4096 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : (4096 : ℝ) ≤ X ^ 2 := by nlinarith
    have h2 : E ≤ X := hEX
    have h3 : 1 = E * u := hEu.symm
    have h4 : E * u * 4096 ≤ X * u * X ^ 2 := by
      have : E * 4096 ≤ X * X ^ 2 := by nlinarith [mul_le_mul h2 h1 (by norm_num) hX0.le]
      nlinarith
    calc 1 * 4096 = E * u * 4096 := by rw [hEu]
      _ ≤ X * u * X ^ 2 := h4
      _ = u * X ^ 3 := by ring
  have b : 0.9 ^ 2 / (E ^ 2 * (E - 0.9)) ≤ (0.0166 : ℝ) * u ^ 2 := by
    have hE9 : 49 ≤ E - 0.9 := by linarith
    have e : u ^ 2 = 1 / E ^ 2 := by rw [hu]; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h2 : 0.0166 * (1 / E ^ 2) * (E ^ 2 * (E - 0.9)) = 0.0166 * (E - 0.9) := by
      field_simp
    rw [h2]
    norm_num
    linarith
  have c : (0.001 : ℝ) / E ^ 2 = 0.001 * u ^ 2 := by rw [hu]; ring
  have d : u + 0.02 * u ^ 2 ≤ 1 / (E - 0.02) := by
    have hE2 : 0 < E - 0.02 := by linarith
    rw [le_div_iff₀ hE2]
    have e1 : (u + 0.02 * u ^ 2) * (E - 0.02) = E * u + 0.02 * u * (E * u) - 0.02 * u - 0.0004 * u ^ 2 := by ring
    rw [e1, hEu]
    nlinarith
  have hA : 0 ≤ 1 / X ^ 3 := by positivity
  have hB : 1 / E = u := hu.symm
  rw [c, hB]
  have hb0 : 0 ≤ 0.9 ^ 2 / (E ^ 2 * (E - 0.9)) := by
    have : 0 < E - 0.9 := by linarith
    positivity
  have hprod : (1 + 1 / X ^ 3) * (u + 0.9 ^ 2 / (E ^ 2 * (E - 0.9))) ≤
      (1 + u / 4096) * (u + 0.0166 * u ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hexp : (1 + u / 4096) * (u + 0.0166 * u ^ 2) ≤ u + 0.0185 * u ^ 2 := by
    have : u ^ 3 ≤ u ^ 2 / 50 := by
      have h : u ^ 3 = u ^ 2 * u := by ring
      rw [h]
      have : 0 ≤ u ^ 2 := by positivity
      nlinarith
    nlinarith
  nlinarith

/-- **The second-order bound of the word length.** `S = 2 x⁴`, the chunk sizes are `sPar`; the conditions are on the keys. -/
theorem trieExactW_second (ks : List (ℕ × ℕ)) (yOf cOf : ℕ × ℕ → ℕ) (hok : ∀ k ∈ ks, keyOK (yOf k) (cOf k) k)
    (hc₁ : ∀ k ∈ ks, 667 ≤ cOf k) (hc₂ : ∀ k ∈ ks, cOf k ≤ 847) (hmy₀ : ∀ k ∈ ks, k.1 * yOf k ≤ 1024)
    (hp : (ks.map fun k => k.1 ^ cOf k).prod ≤ (ks.map fun k => k.1 ^ 757).prod)
    (hΛ : 150 ≤ (ks.map fun k => lg₂ (k.1 : ℝ)).sum) {n : ℕ} (hx64 : 64 ≤ Nat.log 2 n) :
    (trieExactW n (2 * (Nat.log 2 n) ^ 4) (sPar yOf n) ks : ℝ) ≤
      (ks.map fun k => lg₂ (k.1 : ℝ)).sum / 8 * (n : ℝ) ^ 2 /
        (lg₂ n - lg₂ (lg₂ n) - 7.59) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hx64
  obtain ⟨x, hxdef⟩ : ∃ x, x = Nat.log 2 n := ⟨_, rfl⟩
  rw [← hxdef] at hx64 ⊢
  have hxn : 2 ^ x ≤ n := by
    rw [hxdef]
    exact Nat.pow_log_le_self 2 hn0
  have hpoly := poly_le_two_pow_trie x hx64
  have hX : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  have hX0 : (0 : ℝ) < x := by linarith
  have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hN2 : (2 : ℝ) ^ 17 * (x : ℝ) ^ 6 ≤ n := by exact_mod_cast hpoly.trans hxn
  obtain ⟨hl1, hl2⟩ := logb_bounds hn0
  rw [← hxdef] at hl1 hl2
  have hlgx : (6 : ℝ) ≤ lg₂ (x : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hX
    have h64 : lg₂ 64 = 6 := by
      have : (64 : ℝ) = 2 ^ 6 := by norm_num
      rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    linarith
  have hlgx' : lg₂ (x : ℝ) ≤ x - 58 := lg_le_sub hX
  obtain ⟨D, hD⟩ : ∃ D, D = lg₂ n - lg₂ (x : ℝ) := ⟨_, rfl⟩
  have hD58 : 58 ≤ D := by linarith
  have hDx : D ≤ x + 1 - 6 := by linarith
  have hmono : lg₂ (lg₂ (n : ℝ)) ≥ lg₂ (x : ℝ) := Real.logb_le_logb_of_le (by norm_num) hX0 hl1
  have hf : lg₂ n - lg₂ (lg₂ n) - 7.59 ≤ D - 7.59 := by linarith
  have hf0 : 0 < lg₂ n - lg₂ (lg₂ n) - 7.59 := by
    have := lg_le_sub (y := lg₂ (n : ℝ)) (by linarith)
    linarith
  -- apply `trieExactW_le`
  have hc1R : ∀ k ∈ ks, (6.67 : ℝ) ≤ (cOf k : ℝ) / 100 := fun k hk => by
    have : (667 : ℝ) ≤ cOf k := by exact_mod_cast hc₁ k hk
    linarith
  have hc2R : ∀ k ∈ ks, (cOf k : ℝ) / 100 ≤ 8.47 := fun k hk => by
    have : (cOf k : ℝ) ≤ 847 := by exact_mod_cast hc₂ k hk
    linarith
  have hW := trieExactW_le ks yOf (fun k => (cOf k : ℝ) / 100)
    (fun k hk => keyReal_of_ok (hok k hk)) (n := n)
    (by rw [← hxdef]; omega)
    (fun k hk => by
      rw [← hxdef]
      have a := hmy₀ k hk
      have b : k.1 * (x * yOf k) ≤ 1024 * x := by
        calc k.1 * (x * yOf k) = x * (k.1 * yOf k) := by ring
          _ ≤ x * 1024 := Nat.mul_le_mul_left _ a
          _ = 1024 * x := by ring
      refine b.trans (le_trans ?_ (hpoly.trans hxn))
      have h1 : x ≤ x ^ 6 := Nat.le_self_pow (by norm_num) x
      calc 1024 * x ≤ 2 ^ 17 * x := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ _ := Nat.mul_le_mul_left _ h1)
    (by
      rw [← hxdef]
      refine le_trans ?_ (hpoly.trans hxn)
      have h1 : x ^ 4 ≤ x ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      calc 4000 * x ^ 4 ≤ 2 ^ 17 * x ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ _ := Nat.mul_le_mul_left _ h1)
    (fun k hk => by
      rw [← hxdef, ← hD]
      have := hc2R k hk
      linarith)
    (fun k hk => by
      rw [← hxdef, ← hD]
      have := hc1R k hk
      linarith)
  rw [← hxdef, ← hD] at hW
  refine hW.trans ?_
  -- the average
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = (ks.map fun k => lg₂ (k.1 : ℝ)).sum := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ ⊢
  obtain ⟨E, hE⟩ : ∃ E, E = D - 7.57 := ⟨_, rfl⟩
  have hE50 : 50 ≤ E := by rw [hE]; linarith
  have hEX : E ≤ x := by rw [hE]; linarith
  have hsum : (ks.map fun k => lg₂ (k.1 : ℝ) / (D - (cOf k : ℝ) / 100)).sum ≤
      Λ * (1 / E + 0.9 ^ 2 / (E ^ 2 * (E - 0.9))) := by
    have h1 := sum_div_le ks (fun k => lg₂ (k.1 : ℝ)) (fun k => (cOf k : ℝ) / 100 - (757 : ℕ) / 100) E 0.9
      (by linarith) (by norm_num)
      (fun k hk => Real.logb_nonneg (by norm_num) (by
        have : 2 ≤ k.1 := (hok k hk).1
        have h : (2 : ℝ) ≤ k.1 := by exact_mod_cast this
        linarith))
      (fun k hk => by
        have a := hc1R k hk
        have b := hc2R k hk
        rw [abs_le]
        norm_num
        constructor <;> linarith)
    have h2 := weighted_le ks cOf 757 (fun k hk => by have := (hok k hk).1; omega) hp
    have e1 : (ks.map fun k => lg₂ (k.1 : ℝ) / (D - (cOf k : ℝ) / 100)) =
        ks.map fun k => lg₂ (k.1 : ℝ) / (E - ((cOf k : ℝ) / 100 - (757 : ℕ) / 100)) := by
      apply List.map_congr_left
      intro k _
      congr 1
      rw [hE]
      push_cast
      ring
    rw [e1]
    refine h1.trans ?_
    rw [← hΛdef]
    have h3 : (ks.map fun k => lg₂ (k.1 : ℝ) * ((cOf k : ℝ) / 100 - (757 : ℕ) / 100)).sum * (1 / E ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h2 (by positivity)
    linarith
  -- the base
  have hbase : ((3 * n + 406 + 2200 * ((n / 2 - 1) * (2 * x ^ 4 + 2)) : ℕ) : ℝ) ≤
      Λ / 8 * (n : ℝ) ^ 2 * (0.001 / E ^ 2) := by
    have hr : ((n / 2 - 1 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      have : 2 * (n / 2 - 1) ≤ n := by omega
      have h : (2 : ℝ) * ((n / 2 - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hx4 : (1 : ℝ) ≤ (x : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    have hx4' : (27 : ℝ) ≤ (x : ℝ) ^ 4 := by
      have : (64 : ℝ) ^ 4 ≤ (x : ℝ) ^ 4 := by gcongr
      linarith
    have h1 : ((3 * n + 406 + 2200 * ((n / 2 - 1) * (2 * x ^ 4 + 2)) : ℕ) : ℝ) ≤ 2300 * n * (x : ℝ) ^ 4 := by
      push_cast
      have h2 : ((n / 2 - 1 : ℕ) : ℝ) * (2 * (x : ℝ) ^ 4 + 2) ≤ (n : ℝ) / 2 * (2 * (x : ℝ) ^ 4 + 2) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      push_cast at hr h2
      have h3 : (n : ℝ) * (x : ℝ) ^ 4 ≥ 27 * n := by nlinarith
      nlinarith
    refine h1.trans ?_
    have hE2 : (0 : ℝ) < E ^ 2 := by positivity
    have hEx2 : E ^ 2 ≤ (x : ℝ) ^ 2 := by
      have : 0 ≤ E := by linarith
      gcongr
    have h4 : 2300 * (x : ℝ) ^ 4 * E ^ 2 ≤ 18 * 0.001 * (n : ℝ) := by
      have a : 2300 * (x : ℝ) ^ 4 * E ^ 2 ≤ 2300 * (x : ℝ) ^ 4 * (x : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hEx2 (by positivity)
      have b : 2300 * (x : ℝ) ^ 4 * (x : ℝ) ^ 2 = 2300 * (x : ℝ) ^ 6 := by ring
      have c : (0 : ℝ) ≤ (x : ℝ) ^ 6 := by positivity
      norm_num at hN2 ⊢
      linarith
    have e : Λ / 8 * (n : ℝ) ^ 2 * (0.001 / E ^ 2) = (Λ / 8) * 0.001 * (n : ℝ) ^ 2 / E ^ 2 := by ring
    rw [e, le_div_iff₀ hE2]
    have hΛ8 : (18 : ℝ) ≤ Λ / 8 := by linarith
    have h5 : 2300 * (n : ℝ) * (x : ℝ) ^ 4 * E ^ 2 = (n : ℝ) * (2300 * (x : ℝ) ^ 4 * E ^ 2) := by ring
    rw [h5]
    have h6 : (n : ℝ) * (2300 * (x : ℝ) ^ 4 * E ^ 2) ≤ (n : ℝ) * (18 * 0.001 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h4 hN.le
    have h7 : (n : ℝ) * (18 * 0.001 * (n : ℝ)) ≤ Λ / 8 * 0.001 * (n : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ 0.001 * (n : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  -- assemble
  have hnum := final_numeric hE50 hEX hX
  have hA0 : 0 ≤ Λ / 8 * (n : ℝ) ^ 2 := by
    have : 0 ≤ Λ := by linarith
    positivity
  have h1X : 0 ≤ (n : ℝ) ^ 2 / 8 * (1 + 1 / (x : ℝ) ^ 3) := by positivity
  have hmain := mul_le_mul_of_nonneg_left hsum h1X
  have hfin := mul_le_mul_of_nonneg_left hnum hA0
  have e2 : E - 0.02 = D - 7.59 := by rw [hE]; ring
  rw [e2] at hfin
  have hgoal : Λ / 8 * (n : ℝ) ^ 2 * (1 / (D - 7.59)) ≤ Λ / 8 * (n : ℝ) ^ 2 / (lg₂ n - lg₂ (lg₂ n) - 7.59) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hA0 hf0 hf
  refine le_trans ?_ hgoal
  refine le_trans ?_ hfin
  have e3 : Λ / 8 * (n : ℝ) ^ 2 * ((1 + 1 / (x : ℝ) ^ 3) * (1 / E + 0.9 ^ 2 / (E ^ 2 * (E - 0.9))) + 0.001 / E ^ 2) =
      (n : ℝ) ^ 2 / 8 * (1 + 1 / (x : ℝ) ^ 3) * (Λ * (1 / E + 0.9 ^ 2 / (E ^ 2 * (E - 0.9)))) +
        Λ / 8 * (n : ℝ) ^ 2 * (0.001 / E ^ 2) := by ring
  rw [e3, add_comm]
  exact add_le_add hmain hbase

end RubiksGN
