import RubiksGN.MainTight
import RubiksGN.TrieProgram
import RubiksGN.TrieLimit
import RubiksGN.TrieOctaves

/-!
# God's number of the cube group: the second-order term, with trie slots

* `godLabelled_second_order_trie`: `godLabelled μ n ≤ (log₂(24!/2)/4) n² / (log₂ n - log₂ log₂ n - 7.59)` for `n ≥ 2⁶⁴`.
* `main_tight'`: the tight bounds with this denominator.
* `explicit_100`, `main_explicit'`, `explicit_64`, …: explicit bounds `C n² / log₂ n`, from `(100, 567)` to `(2¹⁰²⁴, 19.9)`.

Here `7.59 = 7.57 + 0.02`: `7.57` is the weighted average, with weights `log₂ m`, of the constants `c_k` of the 42 lists (from
`6.69` to `7.99`, see `trieTable`), each being `log₂ y + R/y` at the ends of an interval of ratio `m`, for `R ≈ 8 w / (m - 1)`.
-/

namespace RubiksGN

/-! ### The keys of the exact lists -/

/-- The keys `(m, w)` of the 42 lists: the size, and the total length of the templates. -/
abbrev exactKeys : List (ℕ × ℕ) := exactLists.map tKey

/-- The keys, as an explicit list. -/
def exactKeysList : List (ℕ × ℕ) := [(24, 116), (24, 116), (23, 101), (23, 101), (22, 115), (22, 114), (21, 90), (21, 91),
    (20, 103), (20, 103), (19, 109), (18, 97), (17, 97), (16, 87), (15, 77), (14, 71), (13, 67), (12, 59), (11, 56), (10, 47),
    (9, 40), (8, 36), (7, 28), (6, 23), (19, 108), (18, 97), (17, 96), (16, 88), (15, 76), (14, 70), (13, 67), (12, 60),
    (11, 57), (10, 46), (9, 41), (8, 35), (7, 29), (6, 24), (5, 32), (12, 59), (5, 32), (12, 59)]

theorem exactKeys_eq : exactKeys = exactKeysList := by
  decide +kernel

/-- The parameter `y` and the constant `c` (in hundredths) of a key. -/
def trieTable : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((5, 32), (22, 738)), ((6, 23), (12, 669)), ((6, 24), (13, 679)), ((7, 28), (12, 685)), ((7, 29), (12, 687)),
   ((8, 35), (12, 701)), ((8, 36), (12, 703)), ((9, 40), (11, 711)), ((9, 41), (12, 715)), ((10, 46), (11, 719)),
   ((10, 47), (12, 726)), ((11, 56), (12, 739)), ((11, 57), (12, 740)), ((12, 59), (11, 738)), ((12, 60), (11, 744)),
   ((13, 67), (11, 753)), ((14, 70), (11, 756)), ((14, 71), (11, 756)), ((15, 76), (11, 764)), ((15, 77), (11, 764)),
   ((16, 87), (11, 773)), ((16, 88), (11, 774)), ((17, 96), (11, 783)), ((17, 97), (11, 788)), ((18, 97), (11, 787)),
   ((19, 108), (11, 794)), ((19, 109), (11, 795)), ((20, 103), (10, 787)), ((21, 90), (8, 762)), ((21, 91), (8, 762)),
   ((22, 114), (10, 799)), ((22, 115), (10, 799)), ((23, 101), (8, 773)), ((24, 116), (9, 795))]

/-- The parameter of a key. -/
def tY (k : ℕ × ℕ) : ℕ := ((trieTable.lookup k).map Prod.fst).getD 1

/-- The constant of a key, in hundredths. -/
def tC (k : ℕ × ℕ) : ℕ := ((trieTable.lookup k).map Prod.snd).getD 800

theorem keys_ok : ∀ k ∈ exactKeys, keyOK (tY k) (tC k) k := by
  rw [exactKeys_eq, exactKeysList]
  decide +kernel

theorem keys_low : ∀ k ∈ exactKeys, 667 ≤ tC k := by
  rw [exactKeys_eq, exactKeysList]
  decide +kernel

theorem keys_high : ∀ k ∈ exactKeys, tC k ≤ 847 := by
  rw [exactKeys_eq, exactKeysList]
  decide +kernel

theorem keys_my : ∀ k ∈ exactKeys, k.1 * tY k ≤ 1024 := by
  rw [exactKeys_eq, exactKeysList]
  decide +kernel

/-- The weighted average of the constants is at most `7.57`. -/
theorem keys_prod : (exactKeys.map fun k => k.1 ^ tC k).prod ≤ (exactKeys.map fun k => k.1 ^ 757).prod := by
  rw [exactKeys_eq, exactKeysList]
  decide +kernel

theorem sum_lg_keys : (exactKeys.map fun k => Real.logb 2 (k.1 : ℝ)).sum = 2 * Real.logb 2 (Nat.factorial 24 / 2 : ℕ) := by
  rw [← sumLog_exactMs, sumLog, exactMs, exactKeys, List.map_map, List.map_map]
  rfl

theorem keys_lambda : (150 : ℝ) ≤ (exactKeys.map fun k => Real.logb 2 (k.1 : ℝ)).sum := by
  rw [sum_lg_keys]
  have := lgE_div_four
  linarith

/-- The round scheme with trie slots and the exact lists, for any admissible parameters. -/
theorem godLabelled_le_trie (μ : Metric) {n : ℕ} (hn : 3 ≤ n) {S : ℕ} {sOf : ℕ × ℕ → ℕ}
    (hS0 : 0 < S) (hS : Even S) (hs : ∀ k ∈ exactKeys, 0 < sOf k) :
    (godLabelled μ n : ℝ) ≤ trieExactW n S sOf exactKeys := by
  exact_mod_cast godLabelled_le_trieExactW μ hn exactLists exact_universal S hS0 hS sOf hs 8 exactLists_tmplLen

/-! ### The second-order term -/

/-- **No `ε`, with denominator `log₂ n - log₂ log₂ n - 7.59`, for every `n ≥ 2 ^ 64`.** -/
theorem godLabelled_second_order_trie (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (godLabelled μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 2 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := by
  have hx : 64 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hn3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hn0 : n ≠ 0 := by omega
  have hxn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpoly := poly_le_two_pow_trie _ hx
  have hxpos : 0 < Nat.log 2 n := by omega
  have hsum := trieExactW_second exactKeys tY tC keys_ok keys_low keys_high keys_my keys_prod keys_lambda hx
  have hs : ∀ k ∈ exactKeys, 0 < sPar tY n k := by
    intro k hk
    have hm : 2 ≤ k.1 := (keys_ok k hk).1
    have hy : 1 ≤ tY k := (keys_ok k hk).2.1
    apply Nat.log_pos (by omega)
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have a := keys_my k hk
    have b : k.1 * (Nat.log 2 n * tY k) ≤ 1024 * Nat.log 2 n := by
      calc k.1 * (Nat.log 2 n * tY k) = Nat.log 2 n * (k.1 * tY k) := by ring
        _ ≤ Nat.log 2 n * 1024 := Nat.mul_le_mul_left _ a
        _ = _ := by ring
    refine b.trans (le_trans ?_ (hpoly.trans hxn))
    have h1 : Nat.log 2 n ≤ Nat.log 2 n ^ 6 := Nat.le_self_pow (by norm_num) _
    calc 1024 * Nat.log 2 n ≤ 2 ^ 17 * Nat.log 2 n := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ _ := Nat.mul_le_mul_left _ h1
  have h1 := godLabelled_le_trie μ hn3 (S := 2 * Nat.log 2 n ^ 4) (sOf := sPar tY n) (by positivity)
    (even_two_mul _) hs
  refine h1.trans (hsum.trans (le_of_eq ?_))
  rw [sum_lg_keys]
  ring

/-- **The tight bounds, with the improved denominator.** The same `19.5…` on both sides. -/
theorem main_tight' (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (19.509 * ((n : ℝ) + 1) * ((n : ℝ) - 3) - 1) / (Real.logb 2 n + dMove μ) ≤ godLabelled μ n ∧
    (godLabelled μ n : ℝ) ≤
      19.51 * (n : ℝ) ^ 2 / (Real.logb 2 n - Real.logb 2 (Real.logb 2 n) - 7.59) := by
  have h3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  refine ⟨lowerCommute_labelled μ h3, (godLabelled_second_order_trie μ hn).trans ?_⟩
  have hl : (64 : ℝ) ≤ Real.logb 2 n := by
    have h1 : ((2 : ℝ) ^ 64) ≤ n := by exact_mod_cast hn
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    push_cast at h2
    linarith
  have h0 := lg_le_sub hl
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_right lgE_div_four_le (by positivity)

/-! ### Explicit bounds on an octave -/

/-- The bound on the word length at `n`, times `4 S`. -/
def octF (n S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) : ℕ :=
  trieRounds S sOf ks * n ^ 2 + (4 * S * (3 + 1100 * (S + 2)) + 4 * trieSlots S sOf ks) * n +
    (1624 * S + 8 * S * trieSlots S sOf ks)

theorem trieExactW_scaled (m S : ℕ) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) :
    4 * S * trieExactW m S sOf ks ≤ octF m S sOf ks := by
  obtain ⟨r, hr⟩ : ∃ r, r = m / 2 - 1 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = trieRounds S sOf ks := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = trieSlots S sOf ks := ⟨_, rfl⟩
  have h2r : 2 * r ≤ m := by omega
  simp only [trieExactW, octF, ← hr, ← hR, ← hC]
  have h1 : S * (r ^ 2 / S) ≤ r ^ 2 := Nat.mul_div_le _ _
  have h2 : S * (r / S) ≤ r := Nat.mul_div_le _ _
  have a1 : 4 * r ^ 2 ≤ m ^ 2 := by nlinarith
  have a2 : 4 * S * (R * (r ^ 2 / S)) ≤ R * m ^ 2 := by
    calc 4 * S * (R * (r ^ 2 / S)) = R * (4 * (S * (r ^ 2 / S))) := by ring
      _ ≤ R * (4 * r ^ 2) := by gcongr
      _ ≤ R * m ^ 2 := Nat.mul_le_mul_left _ a1
  have a3 : 4 * S * (2 * (r / S + 1) * C) ≤ (4 * m + 8 * S) * C := by
    calc 4 * S * (2 * (r / S + 1) * C) = (8 * (S * (r / S)) + 8 * S) * C := by ring
      _ ≤ (8 * r + 8 * S) * C := by gcongr
      _ ≤ (4 * m + 8 * S) * C := Nat.mul_le_mul_right _ (by omega)
  have a4 : 4 * S * (2200 * (r * (S + 2))) ≤ 4 * S * (1100 * (S + 2)) * m := by
    calc 4 * S * (2200 * (r * (S + 2))) = 4 * S * (1100 * (S + 2)) * (2 * r) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h2r
  have e : 4 * S * (3 * m + 406 + 2200 * (r * (S + 2)) + R * (r ^ 2 / S) + 2 * (r / S + 1) * C) =
      12 * S * m + 1624 * S + 4 * S * (2200 * (r * (S + 2))) + 4 * S * (R * (r ^ 2 / S)) +
        4 * S * (2 * (r / S + 1) * C) := by ring
  have e2 : R * m ^ 2 + (4 * S * (3 + 1100 * (S + 2)) + 4 * C) * m + (1624 * S + 8 * S * C) =
      R * m ^ 2 + 12 * S * m + 4 * S * (1100 * (S + 2)) * m + (4 * m + 8 * S) * C + 1624 * S := by ring
  rw [e, e2]
  omega

/-- The bound decreases in `n`, relative to `n²`. -/
theorem octF_mono (n m S : ℕ) (hnm : n ≤ m) (sOf : ℕ × ℕ → ℕ) (ks : List (ℕ × ℕ)) :
    n ^ 2 * octF m S sOf ks ≤ m ^ 2 * octF n S sOf ks := by
  simp only [octF]
  obtain ⟨R, -⟩ : ∃ R, R = trieRounds S sOf ks := ⟨_, rfl⟩
  generalize trieRounds S sOf ks = R'
  generalize (4 * S * (3 + 1100 * (S + 2)) + 4 * trieSlots S sOf ks) = B
  generalize (1624 * S + 8 * S * trieSlots S sOf ks) = G
  have h1 : n ^ 2 * (B * m) ≤ m ^ 2 * (B * n) := by
    calc n ^ 2 * (B * m) = (n * B) * (n * m) := by ring
      _ ≤ (n * B) * (m * m) := by gcongr
      _ = _ := by ring
  have h2 : n ^ 2 * G ≤ m ^ 2 * G := by gcongr
  nlinarith

/-- The chunk size of a key on an octave. -/
def octS (x : ℕ) (k : ℕ × ℕ) : ℕ :=
  (((octTable.lookup x).map fun e => e.2).bind fun e => e.lookup k).getD 1

/-- The block size of an octave. -/
def octB (x : ℕ) : ℕ := ((octTable.lookup x).map Prod.fst).getD 2

/-- The check of an octave for the constant `C`. -/
def octOK (C x : ℕ) : Bool :=
  decide (0 < octB x) && decide (octB x % 2 = 0) && exactKeysList.all (fun k => decide (0 < octS x k)) &&
    decide ((x + 1) * octF (2 ^ x) (octB x) (octS x) exactKeysList ≤ C * (4 * octB x) * (2 ^ x) ^ 2)

/-- The bound on one octave. -/
theorem godLabelled_le_of_octave (μ : Metric) {C x n : ℕ} (h : octOK C x = true) (hx : 2 ≤ x)
    (hn : 2 ^ x ≤ n) (hn2 : n < 2 ^ (x + 1)) :
    (godLabelled μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  simp only [octOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h0, he⟩, hs⟩, hc⟩ := h
  have hn3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
    omega
  have hG := godLabelled_le_trie μ hn3 (S := octB x) (sOf := octS x) h0 (Nat.even_iff.2 he)
    (by rw [exactKeys_eq]; exact hs)
  rw [exactKeys_eq] at hG
  obtain ⟨W, hW⟩ : ∃ W, W = trieExactW n (octB x) (octS x) exactKeysList := ⟨_, rfl⟩
  rw [← hW] at hG
  have h1 := trieExactW_scaled n (octB x) (octS x) exactKeysList
  rw [← hW] at h1
  have h2 := octF_mono (2 ^ x) n (octB x) hn (octS x) exactKeysList
  have hpos : 0 < 4 * octB x * (2 ^ x) ^ 2 := by positivity
  have hnat : (x + 1) * W ≤ C * n ^ 2 := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc (x + 1) * W * (4 * octB x * (2 ^ x) ^ 2)
        = (x + 1) * (2 ^ x) ^ 2 * (4 * octB x * W) := by ring
      _ ≤ (x + 1) * (2 ^ x) ^ 2 * octF n (octB x) (octS x) exactKeysList := Nat.mul_le_mul_left _ h1
      _ = (x + 1) * ((2 ^ x) ^ 2 * octF n (octB x) (octS x) exactKeysList) := by ring
      _ ≤ (x + 1) * (n ^ 2 * octF (2 ^ x) (octB x) (octS x) exactKeysList) := Nat.mul_le_mul_left _ h2
      _ = n ^ 2 * ((x + 1) * octF (2 ^ x) (octB x) (octS x) exactKeysList) := by ring
      _ ≤ n ^ 2 * (C * (4 * octB x) * (2 ^ x) ^ 2) := Nat.mul_le_mul_left _ hc
      _ = _ := by ring
  have hN : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hx0 : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hN
  rw [le_div_iff₀ hx0]
  have hl : Real.logb 2 (n : ℝ) ≤ (x : ℝ) + 1 := by
    have h3 : (n : ℝ) ≤ (2 : ℝ) ^ (x + 1) := by exact_mod_cast hn2.le
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) h3
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h4
    push_cast at h4
    linarith
  have hr : ((x : ℝ) + 1) * (W : ℝ) ≤ C * (n : ℝ) ^ 2 := by exact_mod_cast hnat
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  calc (godLabelled μ n : ℝ) * Real.logb 2 n ≤ W * Real.logb 2 n :=
        mul_le_mul_of_nonneg_right hG hx0.le
    _ ≤ W * ((x : ℝ) + 1) := mul_le_mul_of_nonneg_left hl hW0
    _ = ((x : ℝ) + 1) * W := by ring
    _ ≤ _ := hr

/-- The check of all octaves from `k` to `63`. -/
def octRange (k C : ℕ) : Bool := (List.range (64 - k)).all fun i => octOK C (k + i)

theorem godLabelled_le_of_range (μ : Metric) {k C n : ℕ} (h : octRange k C = true) (hk : 2 ≤ k)
    (hn : 2 ^ k ≤ n) (hn2 : n < 2 ^ 64) :
    (godLabelled μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have hx1 : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ k := by positivity
    omega
  have hx2 : Nat.log 2 n < 64 := Nat.log_lt_of_lt_pow hn0 hn2
  simp only [octRange, List.all_eq_true, List.mem_range] at h
  have hc := h (Nat.log 2 n - k) (by omega)
  rw [Nat.add_sub_cancel' hx1] at hc
  exact godLabelled_le_of_octave μ hc (by omega) (Nat.pow_log_le_self 2 hn0)
    (Nat.lt_pow_succ_log_self (by norm_num) n)

/-! ### Large `n`, from the second-order bound -/

/-- `t / (t - log₂ t - 7.59)` decreases, in the form needed. -/
theorem ratio_le {t k a : ℝ} (hk : 64 ≤ k) (hlg : Real.logb 2 k = a) (ha : 0 ≤ a) (ht : k ≤ t) :
    t * (k - a - 7.59) ≤ k * (t - Real.logb 2 t - 7.59) := by
  have hk0 : 0 < k := by linarith
  have ht0 : 0 < t := by linarith
  have hsplit : Real.logb 2 t = a + Real.logb 2 (t / k) := by
    rw [← hlg, ← Real.logb_mul hk0.ne' (by positivity)]
    congr 1
    field_simp
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hq : 0 < t / k := by positivity
  have h1 : Real.log (t / k) ≤ t / k - 1 := Real.log_le_sub_one_of_pos hq
  have hq1 : 0 ≤ t / k - 1 := by
    have : 1 ≤ t / k := by
      rw [le_div_iff₀ hk0]
      linarith
    linarith
  have h2 : Real.logb 2 (t / k) ≤ (t / k - 1) / 0.69 := by
    rw [Real.logb, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have h3 : k * Real.logb 2 (t / k) ≤ (t - k) / 0.69 := by
    have e : (t - k) / 0.69 = k * ((t / k - 1) / 0.69) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 hk0.le
  have h4 : (t - k) / 0.69 ≤ (t - k) * 1.5 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  rw [hsplit]
  nlinarith

/-- From the second-order bound to `C n² / log₂ n`, for `n ≥ 2 ^ (2 ^ a)`. -/
theorem godLabelled_explicit_large (μ : Metric) {a n : ℕ} (ha : 6 ≤ a) (hn : 2 ^ (2 ^ a) ≤ n) {C : ℝ}
    (hC : 19.51 * (2 : ℝ) ^ a ≤ C * ((2 : ℝ) ^ a - a - 7.59)) (hd : 0 < (2 : ℝ) ^ a - a - 7.59) :
    (godLabelled μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have h64 : 64 ≤ 2 ^ a := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hn' : 2 ^ 64 ≤ n := (Nat.pow_le_pow_right (by norm_num) h64).trans hn
  have hmain := (main_tight' μ hn').2
  have hkR : (64 : ℝ) ≤ (2 : ℝ) ^ a := by exact_mod_cast h64
  have ht : (2 : ℝ) ^ a ≤ Real.logb 2 n := by
    have h1 : ((2 : ℝ) ^ (2 ^ a)) ≤ n := by exact_mod_cast hn
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    push_cast at h2
    linarith
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.logb 2 (n : ℝ) := ⟨_, rfl⟩
  rw [← htdef] at hmain ht ⊢
  have hlg : Real.logb 2 ((2 : ℝ) ^ a) = a := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hr := ratio_le hkR hlg (by positivity) ht
  have ht0 : 0 < t := by linarith
  have hf0 : 0 < t - Real.logb 2 t - 7.59 := by
    have := lg_le_sub (y := t) (by linarith)
    linarith
  refine hmain.trans ?_
  rw [div_le_div_iff₀ hf0 ht0]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hkey : 19.51 * t ≤ C * (t - Real.logb 2 t - 7.59) := by
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (2 : ℝ) ^ a := ⟨_, rfl⟩
    rw [← hk] at hC hd hr
    have h1 : 19.51 * t * (k - a - 7.59) ≤ 19.51 * (k * (t - Real.logb 2 t - 7.59)) := by
      calc 19.51 * t * (k - a - 7.59) = 19.51 * (t * (k - a - 7.59)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hr (by norm_num)
    have h2 : 19.51 * (k * (t - Real.logb 2 t - 7.59)) ≤
        C * (k - a - 7.59) * (t - Real.logb 2 t - 7.59) := by
      calc 19.51 * (k * (t - Real.logb 2 t - 7.59)) = (19.51 * k) * (t - Real.logb 2 t - 7.59) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC hf0.le
    have h3 : (19.51 * t) * (k - a - 7.59) ≤ (C * (t - Real.logb 2 t - 7.59)) * (k - a - 7.59) := by
      calc (19.51 * t) * (k - a - 7.59) ≤ C * (k - a - 7.59) * (t - Real.logb 2 t - 7.59) := h1.trans h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hd
  calc 19.51 * (n : ℝ) ^ 2 * t = (n : ℝ) ^ 2 * (19.51 * t) := by ring
    _ ≤ (n : ℝ) ^ 2 * (C * (t - Real.logb 2 t - 7.59)) := mul_le_mul_of_nonneg_left hkey hn2
    _ = _ := by ring

/-- `n ≥ 2 ^ 64`: the constant `24.8`. -/
theorem explicit_64 (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 24.8 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godLabelled_explicit_large μ (a := 6) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-- `n ≥ 2 ^ 128`: the constant `22.1`. -/
theorem explicit_128 (μ : Metric) {n : ℕ} (hn : 2 ^ 128 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 22.1 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godLabelled_explicit_large μ (a := 7) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-- `n ≥ 2 ^ 256`: the constant `20.8`. -/
theorem explicit_256 (μ : Metric) {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 20.8 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godLabelled_explicit_large μ (a := 8) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

set_option exponentiation.threshold 2000 in
/-- `n ≥ 2 ^ 1024`: the constant `19.9`. -/
theorem explicit_1024 (μ : Metric) {n : ℕ} (hn : 2 ^ 1024 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 19.9 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godLabelled_explicit_large μ (a := 10) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-! ### All `n ≥ 2 ^ k` -/

/-- From the range check to all `n ≥ 2 ^ k`. -/
theorem godLabelled_explicit_of_range (μ : Metric) {k C n : ℕ} (h : octRange k C = true) (hk : 2 ≤ k)
    (hC : 25 ≤ C) (hn : 2 ^ k ≤ n) :
    (godLabelled μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  by_cases h64 : n < 2 ^ 64
  · exact godLabelled_le_of_range μ h hk hn h64
  · refine (explicit_64 μ (by omega)).trans ?_
    have hN : (1 : ℝ) < n := by
      have : 1 < n := by
        have : 2 ^ 1 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      exact_mod_cast this
    have hx0 : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hN
    have hCR : (25 : ℝ) ≤ C := by exact_mod_cast hC
    apply div_le_div_of_nonneg_right _ hx0.le
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem octRange_8 : octRange 8 466 = true := by decide +kernel
theorem octRange_9 : octRange 9 298 = true := by decide +kernel
theorem octRange_10 : octRange 10 207 = true := by decide +kernel
theorem octRange_12 : octRange 12 125 = true := by decide +kernel
theorem octRange_16 : octRange 16 61 = true := by decide +kernel
theorem octRange_20 : octRange 20 45 = true := by decide +kernel
theorem octRange_24 : octRange 24 38 = true := by decide +kernel
theorem octRange_32 : octRange 32 31 = true := by decide +kernel
theorem octRange_40 : octRange 40 29 = true := by decide +kernel
theorem octRange_48 : octRange 48 27 = true := by decide +kernel

/-- **Explicit upper bounds**: `godLabelled μ n ≤ C n² / log₂ n` for `n ≥ N₀`, for a table of pairs `(N₀, C)`. -/
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
    (2 ^ 64 ≤ n → (godLabelled μ n : ℝ) ≤ 24.8 * (n : ℝ) ^ 2 / Real.logb 2 n) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => explicit_64 μ h⟩
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_8 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_9 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_10 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_12 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_16 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_20 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_24 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_32 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_40 (by norm_num) (by norm_num) h
  · exact_mod_cast godLabelled_explicit_of_range μ octRange_48 (by norm_num) (by norm_num) h

/-! ### All `n ≥ 100` -/

/-- The check of `n` in `[100, 256)`: the old word length, with `log₂ n` bounded in thirty-seconds. -/
def smallOK (C : ℕ) : Bool :=
  (List.range 156).all fun i =>
    decide (upperW (100 + i) 3 * (Nat.log2 ((100 + i) ^ 32) + 1) ≤ C * 32 * (100 + i) ^ 2)

theorem smallOK_567 : smallOK 567 = true := by decide +kernel

/-- **`n ≥ 100`: the constant `567`**, against `650` in `Main.lean`. -/
theorem explicit_100 (μ : Metric) {n : ℕ} (hn : 100 ≤ n) :
    (godLabelled μ n : ℝ) ≤ 567 * (n : ℝ) ^ 2 / Real.logb 2 n := by
  by_cases h256 : 256 ≤ n
  · refine ((main_explicit' μ n).1 (by norm_num; exact h256)).trans ?_
    have hN : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hx0 : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hN
    apply div_le_div_of_nonneg_right _ hx0.le
    apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  · have h := smallOK_567
    simp only [smallOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    have hc := h (n - 100) (by omega)
    rw [Nat.add_sub_cancel' hn] at hc
    have hN : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hx0 : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hN
    rw [le_div_iff₀ hx0]
    have hG : (godLabelled μ n : ℝ) ≤ upperW n 3 := by
      exact_mod_cast godLabelled_le_upperW μ (by omega) 3 (by norm_num)
    have hl : 32 * Real.logb 2 (n : ℝ) ≤ (Nat.log2 (n ^ 32) : ℝ) + 1 := by
      have h1 : n ^ 32 < 2 ^ (Nat.log2 (n ^ 32) + 1) := Nat.lt_log2_self
      have h2 : (n : ℝ) ^ 32 ≤ (2 : ℝ) ^ (Nat.log2 (n ^ 32) + 1) := by exact_mod_cast h1.le
      have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2
      rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h3
      push_cast at h3
      linarith
    have hr : (upperW n 3 : ℝ) * ((Nat.log2 (n ^ 32) : ℝ) + 1) ≤ 567 * 32 * (n : ℝ) ^ 2 := by
      exact_mod_cast hc
    have hW0 : (0 : ℝ) ≤ upperW n 3 := by positivity
    have h5 : (godLabelled μ n : ℝ) * (32 * Real.logb 2 n) ≤ 567 * 32 * (n : ℝ) ^ 2 :=
      calc (godLabelled μ n : ℝ) * (32 * Real.logb 2 n) ≤ upperW n 3 * (32 * Real.logb 2 n) :=
            mul_le_mul_of_nonneg_right hG (by positivity)
        _ ≤ upperW n 3 * ((Nat.log2 (n ^ 32) : ℝ) + 1) := mul_le_mul_of_nonneg_left hl hW0
        _ ≤ _ := hr
    linarith

end RubiksGN
