import RubiksGN.Constants

/-!
# Explicit lower-order terms

Closed forms that hold from a small threshold onwards, with no `ε`:

* `n ≥ 100`: `(12.88 (n-1)(n-3) - 15.6) / (log₂ n + 3.18) ≤ godColoured μ n`,
* `n ≥ 2¹⁶`: `godLabelled μ n ≤ (275/2) n² / (log₂ n - 2 log₂ log₂ n - 4)`.

They explain the drift of the constants: relative to `n² / log₂ n` the corrections are `-3.18 / log₂ n`
for the lower bound and `+(2 log₂ log₂ n + 4) / log₂ n` for the upper bound.
-/

namespace RubiksGN

variable {n : ℕ}

/-! ### Lower bound -/

/-- The counting inequality with the exact logarithm of the number of moves. -/
theorem log_count_exact (μ : Metric) (hn : 3 ≤ n) :
    (innerOrbits n : ℝ) * LZ ≤ 6 * lg 6 + (godColoured μ n : ℝ) * lg (9 * n + 1) := by
  have h := lower_count μ hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hZ : (0 : ℝ) < Zval := by
    rw [Zval_eq]; norm_num
  have h' : (Zval : ℝ) ^ innerOrbits n ≤ (6 : ℝ) ^ 6 * ((9 * n + 1 : ℝ)) ^ godColoured μ n := by
    exact_mod_cast h
  have h2 := lg_mono (by positivity) h'
  rw [lg_pow, lg_mul (by positivity) (by positivity), lg_pow, lg_pow] at h2
  push_cast at h2
  simpa only [LZ] using h2

theorem lg901_upper : lg (901 / 100) ≤ 3.18 := by
  have h : ((901 / 100 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 318 := by
    have hn : 901 ^ 100 ≤ 2 ^ 318 * 100 ^ 100 := by decide +kernel
    have hr : ((901 : ℝ) ^ 100) ≤ (2 : ℝ) ^ 318 * (100 : ℝ) ^ 100 := by exact_mod_cast hn
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact hr
  have h2 := lg_mono (by positivity) h
  rw [lg_two_pow, lg_pow] at h2
  push_cast at h2
  linarith

/-- **The lower bound with its explicit lower-order terms.** -/
theorem lower_second_order (μ : Metric) (hn : 100 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 15.6) / (lg n + 3.18) ≤ godColoured μ n := by
  have hN : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < lg n := Real.logb_pos (by norm_num) (by linarith)
  have hc := log_count_exact μ (by omega : 3 ≤ n)
  have hin := innerOrbits_lower (by omega : 3 ≤ n)
  have hL := LZ_lower
  have hI0 : (0 : ℝ) ≤ innerOrbits n := by positivity
  have h9 : lg (9 * n + 1) ≤ lg n + 3.18 := by
    have hle : (9 * n + 1 : ℝ) ≤ (901 / 100) * n := by linarith
    have := lg_mono (by positivity) hle
    rw [lg_mul (by norm_num) (by positivity)] at this
    linarith [lg901_upper]
  have hG : (0 : ℝ) ≤ godColoured μ n := by positivity
  have h1 := mul_le_mul_of_nonneg_left h9 hG
  have h2 : (51.52 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 3) / 4) ≤ (innerOrbits n : ℝ) * LZ := by
    calc (51.52 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 3) / 4) ≤ 51.52 * (innerOrbits n : ℝ) :=
          mul_le_mul_of_nonneg_left hin (by norm_num)
      _ ≤ LZ * (innerOrbits n : ℝ) := mul_le_mul_of_nonneg_right hL hI0
      _ = _ := mul_comm _ _
  rw [div_le_iff₀ (by linarith)]
  have h6 := lg6_upper
  nlinarith

/-! ### Upper bound -/

theorem hundred_sq_le (L : ℕ) (hL : 16 ≤ L) : 100 * (L + 1) ^ 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ 2 L]
    nlinarith

/-- `log₂ x ≤ x / 4` from `x = 16` on. -/
theorem lg_le_quarter (x : ℝ) (hx : 16 ≤ x) : lg x ≤ x / 4 := by
  have h16 : lg 16 = 4 := by
    have : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [this, lg_two_pow]
    norm_num
  have hsplit : lg x = lg 16 + lg (x / 16) := by
    rw [← lg_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have hlog : Real.log (x / 16) ≤ x / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have htwo : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hq : lg (x / 16) ≤ 4 * (x / 16 - 1) := by
    simp only [lg, Real.logb]
    rw [div_le_iff₀ (by linarith)]
    have hnn : 0 ≤ x / 16 - 1 := by linarith
    nlinarith
  rw [hsplit, h16]
  linarith

/-- The purely arithmetical step. -/
theorem cost_arith (N x D s p r Q : ℝ) (hx : 16 ≤ x) (hN : 100 * x ^ 2 ≤ N) (hD0 : 0 < D)
    (hDx : D ≤ x) (hDs : D + 2.8 ≤ s) (hsx : s ≤ x) (hp0 : 0 ≤ p) (hp : p * x ^ 2 ≤ N)
    (hr0 : 0 ≤ r) (hr : 2 * (r * s) ≤ N) (hQ0 : 0 ≤ Q) (hQ : Q ≤ (2 * s + 4) * p + N + 1) :
    (3 * N + 406 + 275 * ((r + 1) * Q)) * D ≤ 275 / 2 * N ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have hNbig : 1600 * x ≤ N := by nlinarith
  have hN0 : 0 < N := by nlinarith
  -- `D Q ≤ N (D + 2.3125)`
  have hQx : Q * x ^ 2 ≤ (2 * x + 4) * N + (N + 1) * x ^ 2 := by
    have h1 : (2 * s + 4) * p * x ^ 2 ≤ (2 * x + 4) * N := by
      calc (2 * s + 4) * p * x ^ 2 = (2 * s + 4) * (p * x ^ 2) := by ring
        _ ≤ (2 * x + 4) * N := mul_le_mul (by linarith) hp (by positivity) (by linarith)
    have h2 : Q * x ^ 2 ≤ ((2 * s + 4) * p + N + 1) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hQ hx2.le
    nlinarith
  have hDQ : D * Q ≤ N * (D + 2.3125) := by
    have h1 : D * (Q * x ^ 2) ≤ D * ((2 * x + 4) * N + (N + 1) * x ^ 2) :=
      mul_le_mul_of_nonneg_left hQx hD0.le
    have h2 : D * ((2 * x + 4) * N) ≤ x * ((2 * x + 4) * N) :=
      mul_le_mul_of_nonneg_right hDx (by positivity)
    have h3 : x * ((2 * x + 4) * N) ≤ 2.25 * x ^ 2 * N := by
      have : x * (2 * x + 4) ≤ 2.25 * x ^ 2 := by nlinarith
      calc x * ((2 * x + 4) * N) = (x * (2 * x + 4)) * N := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right this hN0.le
    have h4 : D * x ^ 2 ≤ 0.0625 * N * x ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hx2.le
      linarith
    have key : (D * Q) * x ^ 2 ≤ (N * (D + 2.3125)) * x ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right key hx2
  -- `(r + 1) 2 s ≤ N + 2 s`
  have hr1 : (r + 1) * (2 * s) ≤ N + 2 * s := by nlinarith
  have hDQ0 : 0 ≤ D * Q := by positivity
  have hmain : ((r + 1) * (2 * s)) * (D * Q) ≤ (N + 2 * s) * (N * (s - 0.4875)) := by
    apply mul_le_mul hr1 _ hDQ0 (by positivity)
    calc D * Q ≤ N * (D + 2.3125) := hDQ
      _ ≤ N * (s - 0.4875) := mul_le_mul_of_nonneg_left (by linarith) hN0.le
  have hs2 : s ^ 2 ≤ N / 100 := by
    have : s ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hs0.le hsx 2
    linarith
  have hDs' : D * s ≤ N / 100 := by nlinarith
  have h406 : 406 ≤ 0.016 * N := by linarith
  have hsmall : (3 * N + 406) * (D * s) ≤ 3.016 * N * (N / 100) := by
    apply mul_le_mul (by linarith) hDs' (by positivity) (by positivity)
  have hexp : (N + 2 * s) * (N * (s - 0.4875)) ≤ N ^ 2 * s - 0.4875 * N ^ 2 + 2 * s ^ 2 * N := by
    nlinarith [mul_pos hs0 hN0]
  have hs2N : 2 * s ^ 2 * N ≤ 0.02 * N ^ 2 := by nlinarith
  have goal : ((3 * N + 406 + 275 * ((r + 1) * Q)) * D) * s ≤ (275 / 2 * N ^ 2) * s := by
    have e : ((3 * N + 406 + 275 * ((r + 1) * Q)) * D) * s =
        (3 * N + 406) * (D * s) + 275 / 2 * (((r + 1) * (2 * s)) * (D * Q)) := by ring
    rw [e]
    nlinarith [sq_nonneg N]
  exact le_of_mul_le_mul_right goal hs0

/-- **The upper bound with its explicit lower-order terms.** -/
theorem upper_second_order (μ : Metric) (hn : 2 ^ 16 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 275 / 2 * (n : ℝ) ^ 2 / (lg n - 2 * lg (lg n) - 4) := by
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ 16 := by norm_num
    omega
  have hn3 : 3 ≤ n := by
    have : 3 ≤ 2 ^ 16 := by norm_num
    omega
  have rNpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  set L := Nat.log2 n with hLdef
  have hLn : 2 ^ L ≤ n := two_pow_log2_le hn0
  have hL16 : 16 ≤ L := (Nat.le_log2 hn0).2 hn
  have hnL : n < 2 ^ (L + 1) := lt_two_pow_log2
  set x := lg n with hxdef
  have hLx : (L : ℝ) ≤ x := by
    have h : ((2 : ℝ) ^ L) ≤ n := by exact_mod_cast hLn
    have := lg_mono (by positivity) h
    rwa [lg_two_pow] at this
  have hxL : x ≤ (L : ℝ) + 1 := by
    have h : (n : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast hnL.le
    have := lg_mono rNpos h
    rw [lg_two_pow] at this
    push_cast at this
    exact this
  have hx16 : 16 ≤ x := le_trans (by exact_mod_cast hL16) hLx
  have hx0 : 0 < x := by linarith
  -- the block size
  have h100 : 100 * (L + 1) ^ 2 ≤ n := (hundred_sq_le L hL16).trans hLn
  have hsq : 0 < (L + 1) ^ 2 := by positivity
  set M := n / (L + 1) ^ 2 with hMdef
  have hM0 : M ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (by nlinarith) hsq
  set s := Nat.log2 M with hsdef
  have hsM : 2 ^ s ≤ M := two_pow_log2_le hM0
  have hMs : M < 2 ^ (s + 1) := lt_two_pow_log2
  have hMn : M * (L + 1) ^ 2 ≤ n := Nat.div_mul_le_self _ _
  have hnM : n < (L + 1) ^ 2 * (M + 1) := Nat.lt_mul_div_succ n hsq
  -- real versions
  have rL1 : x ≤ (L : ℝ) + 1 := hxL
  have rN100 : 100 * x ^ 2 ≤ n := by
    have h : (100 : ℝ) * ((L : ℝ) + 1) ^ 2 ≤ n := by exact_mod_cast h100
    have h2 : x ^ 2 ≤ ((L : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hx0.le rL1 2
    linarith
  have rp : ((2 : ℝ) ^ s) * x ^ 2 ≤ n := by
    have h1 : 2 ^ s * (L + 1) ^ 2 ≤ n := (Nat.mul_le_mul_right _ hsM).trans hMn
    have h2 : ((2 : ℝ) ^ s) * ((L : ℝ) + 1) ^ 2 ≤ n := by exact_mod_cast h1
    have h3 : x ^ 2 ≤ ((L : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hx0.le rL1 2
    exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans h2
  have hsx : (s : ℝ) ≤ x := by
    have h1 : 2 ^ s ≤ n := hsM.trans (Nat.div_le_self _ _)
    have h : ((2 : ℝ) ^ s) ≤ n := by exact_mod_cast h1
    have := lg_mono (by positivity) h
    rwa [lg_two_pow] at this
  -- `s` is large
  have hlg1716 : lg (17 / 16) ≤ 0.1 := by
    have h : ((17 / 16 : ℝ) ^ 10) ≤ (2 : ℝ) ^ 1 := by norm_num
    have h2 := lg_mono (by positivity) h
    rw [lg_two_pow, lg_pow] at h2
    push_cast at h2
    linarith
  have hlgL : lg ((L : ℝ) + 1) ≤ lg x + 0.1 := by
    have hle : (L : ℝ) + 1 ≤ (17 / 16) * x := by linarith
    have := lg_mono (by positivity) hle
    rw [lg_mul (by norm_num) (by linarith)] at this
    linarith
  have hsbig : x - 2 * lg x - 1.2 ≤ s := by
    have h1 : n ≤ (L + 1) ^ 2 * 2 ^ (s + 1) :=
      hnM.le.trans (Nat.mul_le_mul_left _ hMs)
    have h2 : (n : ℝ) ≤ ((L : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (s + 1) := by exact_mod_cast h1
    have h3 := lg_mono rNpos h2
    rw [lg_mul (by positivity) (by positivity), lg_pow, lg_two_pow] at h3
    push_cast at h3
    change x ≤ _ at h3
    linarith
  set D := x - 2 * lg x - 4 with hDdef
  have hquarter := lg_le_quarter x hx16
  have hlgpos : 0 ≤ lg x := Real.logb_nonneg (by norm_num) (by linarith)
  have hD0 : 0 < D := by rw [hDdef]; linarith
  have hDx : D ≤ x := by rw [hDdef]; linarith
  have hDs : D + 2.8 ≤ s := by rw [hDdef]; linarith
  have hs0 : 0 < s := by
    have : (0 : ℝ) < s := by linarith
    exact_mod_cast this
  -- conclude
  have hG : (godLabelled μ n : ℝ) ≤ upperW n s := by
    exact_mod_cast godLabelled_le_upperW μ hn3 s hs0
  rw [le_div_iff₀ hD0]
  refine (mul_le_mul_of_nonneg_right hG hD0.le).trans ?_
  have hup : upperW n s =
      3 * n + 406 + 275 * (((n / 2 - 1) / s + 1) * ((2 * s + 4) * 2 ^ s + 2 * (n - n / 2))) := rfl
  rw [hup]
  set r := (n / 2 - 1) / s with hr
  set Q := (2 * s + 4) * 2 ^ s + 2 * (n - n / 2) with hQ
  have hrs : r * s ≤ n / 2 - 1 := Nat.div_mul_le_self _ _
  have h2rs : 2 * (r * s) ≤ n := by omega
  have r2rs : (2 : ℝ) * ((r : ℝ) * s) ≤ n := by exact_mod_cast h2rs
  have hQn : Q ≤ (2 * s + 4) * 2 ^ s + n + 1 := by omega
  have rQ : (Q : ℝ) ≤ (2 * (s : ℝ) + 4) * (2 : ℝ) ^ s + n + 1 := by exact_mod_cast hQn
  have := cost_arith (n : ℝ) x D s ((2 : ℝ) ^ s) r Q hx16 rN100 hD0 hDx hDs hsx (by positivity) rp
    (by positivity) r2rs (by positivity) rQ
  push_cast
  exact this

end RubiksGN
