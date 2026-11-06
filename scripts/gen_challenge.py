"""Write Comparator/Challenge.lean: the model definitions, restated verbatim, and the main statements."""
import re
rot=open('RubiksGN/RotData.lean').read()
basic=open('RubiksGN/Basic.lean').read()
def body(s):
    a=s.index("namespace RubiksGN")+len("namespace RubiksGN"); b=s.rindex("end RubiksGN")
    return s[a:b].strip()
main=open('RubiksGN/Main.lean').read()
stm=r'''
/-- **Main theorem**, with explicit constants, for all `n ≥ 100`. -/
theorem main_explicit (μ : Metric) (n : ℕ) (hn : 100 ≤ n) :
    8 * (n : ℝ) ^ 2 / Real.logb 2 n ≤ godColoured μ n ∧
    godColoured μ n ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤ 650 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- **The upper bound for every `n ≥ 3`.** -/
theorem main_upper_all (μ : Metric) (n : ℕ) (hn : 3 ≤ n) :
    (godColoured μ n : ℝ) ≤ 1800 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- **Main theorem**, with the limiting constants. -/
theorem main_asymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ μ : Metric,
      (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 - ε) * (n : ℝ) ^ 2 / Real.logb 2 n ≤
        godColoured μ n ∧
      (godLabelled μ n : ℝ) ≤ (275 / 2 + ε) * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- **Main theorem**, with explicit lower-order terms and no `ε`. -/
theorem main_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 16 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 15.6) / (Real.logb 2 n + 3.18) ≤ godColoured μ n ∧
    godColoured μ n ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      275 / 2 * (n : ℝ) ^ 2 / (Real.logb 2 n - 2 * Real.logb 2 (Real.logb 2 n) - 4) := sorry

/-- `log₂ Z / 4 ≥ 12.88`, where `Z = 24! / (4!)⁶`. -/
theorem lgZ_div_four : (12.88 : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 := sorry

/-- **The limits.** -/
theorem main_limits (μ : Metric) :
    Filter.Tendsto (fun n : ℕ => (godLabelled μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) Filter.atTop
        (nhds (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4)) ∧
      Filter.Tendsto (fun n : ℕ => (godColoured μ n : ℝ) * Real.logb 2 n / (n : ℝ) ^ 2) Filter.atTop
        (nhds (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4)) := sorry

/-- `19.509 ≤ log₂(24!/2) / 4 ≤ 19.51`. -/
theorem lgE_bounds : (19.509 : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 ∧
    Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 ≤ 19.51 := sorry

/-- **The labelled cube, with explicit lower-order terms.** -/
theorem main_labelled_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.89) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      19.51 * (n : ℝ) ^ 2 / (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := sorry

/-- **The coloured cube, lower bound with explicit lower-order terms.** -/
theorem main_coloured_lower (μ : Metric) (n : ℕ) (hn : 100 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured μ n := sorry

/-- **Explicit upper bounds.** -/
theorem main_explicit' (μ : Metric) (n : ℕ) :
    (2 ^ 8 ≤ n → (godLabelled μ n : ℝ) ≤ 466 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 9 ≤ n → (godLabelled μ n : ℝ) ≤ 298 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 10 ≤ n → (godLabelled μ n : ℝ) ≤ 207 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 12 ≤ n → (godLabelled μ n : ℝ) ≤ 125 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 16 ≤ n → (godLabelled μ n : ℝ) ≤ 61 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 20 ≤ n → (godLabelled μ n : ℝ) ≤ 45 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 24 ≤ n → (godLabelled μ n : ℝ) ≤ 38 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 32 ≤ n → (godLabelled μ n : ℝ) ≤ 31 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 40 ≤ n → (godLabelled μ n : ℝ) ≤ 29 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 48 ≤ n → (godLabelled μ n : ℝ) ≤ 27 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 64 ≤ n → (godLabelled μ n : ℝ) ≤ 24.8 * (n : ℝ) ^ 2 / Real.logb 2 n) := sorry

/-- **The coloured cube, with explicit lower-order terms.** -/
theorem main_coloured_second_order (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured μ n ∧
    (godColoured μ n : ℝ) ≤
      12.8821 * (n : ℝ) ^ 2 / (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := sorry

/-- **Explicit upper bounds for the coloured cube.** -/
theorem coloured_explicit (μ : Metric) (n : ℕ) :
    (2 ^ 64 ≤ n → (godColoured μ n : ℝ) ≤ 21.49 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 78 ≤ n → (godColoured μ n : ℝ) ≤ 19.51 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 128 ≤ n → (godColoured μ n : ℝ) ≤ 16.6 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 256 ≤ n → (godColoured μ n : ℝ) ≤ 14.7 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 1024 ≤ n → (godColoured μ n : ℝ) ≤ 13.38 * (n : ℝ) ^ 2 / Real.logb 2 n) := sorry

/-- `n ≥ 100`: the constant `567`. -/
theorem explicit_100 (μ : Metric) {n : ℕ} (hn : 100 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 567 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- **The lower bounds in `htm`, for every `n ≥ 3`.** -/
theorem main_lower_htm (n : ℕ) (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.89) ≤ godColoured .htm n ∧
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.89) ≤ godLabelled .htm n := sorry

/-- **The lower bounds in `qtm`, for every `n ≥ 3`.** -/
theorem main_lower_qtm (n : ℕ) (hn : 3 ≤ n) :
    (12.88 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) / (Real.logb 2 n + 2.33) ≤ godColoured .qtm n ∧
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + 2.33) ≤ godLabelled .qtm n := sorry

/-- `n ≥ 2 ^ 128`: the constant `22.1`. -/
theorem explicit_128 (μ : Metric) {n : ℕ} (hn : 2 ^ 128 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 22.1 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- `n ≥ 2 ^ 256`: the constant `20.8`. -/
theorem explicit_256 (μ : Metric) {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 20.8 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

set_option exponentiation.threshold 2000 in
/-- `n ≥ 2 ^ 1024`: the constant `19.9`. -/
theorem explicit_1024 (μ : Metric) {n : ℕ} (hn : 2 ^ 1024 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 19.9 * (n : ℝ) ^ 2 / Real.logb 2 n := sorry

/-- **The labelled cube: exact main term on both sides**, `n ≥ 2⁶⁴`. -/
theorem main_labelled_exact (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) /
        (Real.logb 2 n + 2.89) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := sorry

/-- **The coloured cube: exact main term on both sides**, `n ≥ 2⁶⁴`. -/
theorem main_coloured_exact (μ : Metric) (n : ℕ) (hn : 2 ^ 64 ≤ n) :
    (Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * ((n : ℝ) - 1) * ((n : ℝ) - 3) - 16.6) /
        (Real.logb 2 n + 2.89) ≤ godColoured μ n ∧
    (godColoured μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := sorry
'''
out="import Mathlib\n\n/-! Comparator challenge: the model of the cube and the main statements, restated verbatim. It imports\nonly Mathlib. `comparator.json` checks that the definitions in `RubiksGN` are identical to these and\nthat the theorems are proved there. Generated by `scripts/gen_challenge.py`. -/\n\nopen Equiv\n\nnamespace RubiksGN\n\n"
out+=body(rot)+"\n\n"+body(basic)+"\n"+stm+"\nend RubiksGN\n"
open('Comparator/Challenge.lean','w').write(out)
