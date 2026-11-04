import RubiksGN.MainColoured
import RubiksGN.TrieLimit

/-!
# God's number of the coloured cube: the second-order term

* `godColoured_second_order`: `godColoured μ n ≤ (log₂(24!/24⁶)/4) n² / (log₂ n - 3 log₂ log₂ n - 7.63)` for `n ≥ 2⁶⁴`.
* `logZ_div_four_le`: `log₂(24!/24⁶)/4 ≤ 12.8821`, and `godColoured_second_order_num`: the same bound with `12.8821`.
* `coloured_explicit`: explicit bounds `C n² / log₂ n`, from `(2⁶⁴, 21.49)` to `(2¹⁰²⁴, 13.38)`.

The parameters. With `t = log₂ n`, `E = t - 3 log₂ t`, a key `k = (m, w)` of ratio `ρ = m / w` has a table entry `g`, and
`s = ⌊(E - log₂ (g / 64)) / log₂ ρ⌋`, so that `ρ^s ≤ 64 n / (g t³)`. All the slot counts `T (2 s L)` are below `κ n / t`, with
`κ = 16 · 0.6932 · 64 / 1964`, because `g log₂ ρ ≥ 1964`: a key with a large ratio has short chunks, so it can have more of them.

Then `7.63 = 6.183 + 1.447`. Here `6.183` is the weighted average, with weights `log₂ ρ`, of the `log₂ (g / 64) + log₂ ρ` (the loss of `log₂ ρ`
is the rounding of `s`), and `1.447 ≥ 4 κ` is the cost of the slots. `S = 2 ⌊t⌋⁴` makes all else negligible.
-/

namespace RubiksGN

/-- Base-2 logarithm. -/
local notation "lg₂" => Real.logb 2

/-! ### The table -/

/-- For each key, the parameter `g` (in units of `1 / 64`), and an upper bound of `log₂ (g / 64) + log₂ (m / w)` in thousandths. -/
def colOrderTable : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((5, 1), (846, 6047)), ((6, 2), (1240, 5862)), ((7, 2), (1087, 5894)), ((7, 3), (1607, 5873)),
   ((8, 2), (982, 5940)), ((8, 3), (1388, 5854)), ((9, 1), (620, 6447)), ((10, 2), (846, 6047)),
   ((11, 1), (568, 6610)), ((11, 2), (799, 6102)), ((12, 1), (548, 6683)), ((12, 2), (760, 6155)),
   ((12, 3), (982, 5940)), ((13, 1), (531, 6754)), ((13, 3), (929, 5976)), ((14, 2), (700, 6259)),
   ((15, 3), (846, 6047)), ((16, 3), (814, 6084)), ((17, 3), (785, 6120)), ((17, 4), (941, 5966)),
   ((18, 3), (760, 6155)), ((18, 4), (906, 5994)), ((19, 4), (874, 6020)), ((20, 3), (718, 6225)),
   ((21, 4), (821, 6074)), ((22, 4), (799, 6102)), ((23, 4), (779, 6130)), ((24, 4), (760, 6155))]

/-- The parameter of a key. -/
def gCol (k : ℕ × ℕ) : ℕ := ((colOrderTable.lookup k).map Prod.fst).getD 64

/-- The constant of a key, in thousandths. -/
def cCol (k : ℕ × ℕ) : ℕ := ((colOrderTable.lookup k).map Prod.snd).getD 6183

/-- The conditions on a key, in integers. -/
def keyColOK (k : ℕ × ℕ) : Prop :=
  0 < k.2 ∧ 2 * k.2 ≤ k.1 ∧ 64 ≤ gCol k ∧ gCol k ≤ 2048 ∧
    2 ^ 1964 * k.2 ^ gCol k ≤ k.1 ^ gCol k ∧
    (gCol k * k.1) ^ 1000 ≤ (64 * k.2) ^ 1000 * 2 ^ cCol k ∧
    5183 ≤ cCol k ∧ cCol k ≤ 7183

instance (k : ℕ × ℕ) : Decidable (keyColOK k) := by
  unfold keyColOK
  infer_instance

/-- A lower bound of `log₂ (m / w)` from integers. -/
theorem rate_of_pow {m w g a : ℕ} (hw : 0 < w) (hm : 0 < m) (h : 2 ^ a * w ^ g ≤ m ^ g) :
    (a : ℝ) ≤ (g : ℝ) * lr (m, w) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : (2 : ℝ) ^ a * (w : ℝ) ^ g ≤ (m : ℝ) ^ g := by exact_mod_cast h
  have h4 : (2 : ℝ) ^ a ≤ ((m : ℝ) / w) ^ g := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact h3
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h5
  exact h5

/-- An upper bound of `log₂ (g / 64) + log₂ (m / w)` from integers. -/
theorem cc_of_pow {m w g c q : ℕ} (hw : 0 < w) (hm : 0 < m) (hg : 0 < g) (hq : 0 < q)
    (h : (g * m) ^ q ≤ (64 * w) ^ q * 2 ^ c) :
    lg₂ ((g : ℝ) / 64) + lr (m, w) ≤ (c : ℝ) / q := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : ((g : ℝ) * m) ^ q ≤ (64 * (w : ℝ)) ^ q * (2 : ℝ) ^ c := by exact_mod_cast h
  have h4 : ((g : ℝ) / 64 * ((m : ℝ) / w)) ^ q ≤ (2 : ℝ) ^ c := by
    have e : (g : ℝ) / 64 * ((m : ℝ) / w) = ((g : ℝ) * m) / (64 * (w : ℝ)) := by
      field_simp
    rw [e, div_pow, div_le_iff₀ (by positivity)]
    linarith
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h4
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_mul (by positivity) (by positivity)] at h5
  rw [le_div_iff₀ hq']
  simp only [lr]
  linarith

/-- The conditions on a key, in real form. -/
structure KeyColReal (k : ℕ × ℕ) : Prop where
  one_le : 1 ≤ lr k
  g1 : (1 : ℝ) ≤ (gCol k : ℝ) / 64
  g2 : (gCol k : ℝ) ≤ 2048
  rate : 1964 ≤ (gCol k : ℝ) * lr k
  cc : lg₂ ((gCol k : ℝ) / 64) + lr k ≤ (cCol k : ℝ) / 1000
  c1 : (5.183 : ℝ) ≤ (cCol k : ℝ) / 1000
  c2 : (cCol k : ℝ) / 1000 ≤ 7.183

theorem keyColReal_of_ok {k : ℕ × ℕ} (h : keyColOK k) : KeyColReal k := by
  obtain ⟨h0, h2, hg1, hg2, hrate, hcc, hc1, hc2⟩ := h
  have hw : (0 : ℝ) < k.2 := by exact_mod_cast h0
  have hm0 : 0 < k.1 := by omega
  have hm : (0 : ℝ) < k.1 := by exact_mod_cast hm0
  have hρ : (0 : ℝ) < (k.1 : ℝ) / k.2 := by positivity
  have hgR : (64 : ℝ) ≤ gCol k := by exact_mod_cast hg1
  refine ⟨?_, ?_, by exact_mod_cast hg2, ?_, ?_, ?_, ?_⟩
  · have h3 : (2 : ℝ) ≤ (k.1 : ℝ) / k.2 := by
      rw [le_div_iff₀ hw]
      exact_mod_cast h2
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) h3
    rw [Real.logb_self_eq_one (by norm_num)] at h4
    exact h4
  · rw [le_div_iff₀ (by norm_num)]
    linarith
  · have h3 := rate_of_pow (m := k.1) (w := k.2) h0 hm0 hrate
    have h4 : (1964 : ℝ) = ((1964 : ℕ) : ℝ) := by norm_num
    rw [h4]
    exact h3
  · have h3 := cc_of_pow (m := k.1) (w := k.2) (q := 1000) h0 hm0 (by omega) (by norm_num) hcc
    have h4 : ((1000 : ℕ) : ℝ) = 1000 := by norm_num
    rw [h4] at h3
    exact h3
  · rw [le_div_iff₀ (by norm_num)]
    have : (5183 : ℝ) ≤ cCol k := by exact_mod_cast hc1
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    have : (cCol k : ℝ) ≤ 7183 := by exact_mod_cast hc2
    linarith

/-! ### The parameters -/

/-- `E = log₂ n - 3 log₂ log₂ n`. -/
noncomputable def eCol (n : ℕ) : ℝ := lg₂ n - 3 * lg₂ (lg₂ n)

/-- The chunk size of a key. -/
noncomputable def sCol (n : ℕ) (k : ℕ × ℕ) : ℕ := ⌊(eCol n - lg₂ ((gCol k : ℝ) / 64)) / lr k⌋₊

/-- The slot bound of a key. -/
noncomputable def tCol (n : ℕ) (k : ℕ × ℕ) : ℕ :=
  ⌈((k.1 : ℝ) / k.2) ^ sCol n k * (Real.log (n : ℝ) + 1) + 1⌉₊

/-- The slots of a pass. -/
noncomputable def cslotCol (n : ℕ) : ℕ := ⌊(16 * 0.6932 * 64 / 1964 : ℝ) * n / lg₂ n⌋₊

theorem sCol_facts {n : ℕ} {k : ℕ × ℕ} (hk : KeyColReal k) (hE : (cCol k : ℝ) / 1000 < eCol n) :
    (sCol n k : ℝ) * lr k ≤ eCol n - lg₂ ((gCol k : ℝ) / 64) ∧ 1 ≤ sCol n k ∧
      1 / (sCol n k : ℝ) ≤ lr k / (eCol n - (cCol k : ℝ) / 1000) := by
  obtain ⟨β, hβ⟩ : ∃ β, β = eCol n - lg₂ ((gCol k : ℝ) / 64) := ⟨_, rfl⟩
  have hl : 0 < lr k := by linarith [hk.one_le]
  have hcc := hk.cc
  have hβl : lr k < β := by rw [hβ]; linarith
  have hβ0 : 0 < β / lr k := by
    apply div_pos _ hl
    linarith
  have hs : sCol n k = ⌊β / lr k⌋₊ := by rw [sCol, hβ]
  have h1 : (sCol n k : ℝ) ≤ β / lr k := by
    rw [hs]
    exact Nat.floor_le hβ0.le
  have h2 : β / lr k < (sCol n k : ℝ) + 1 := by
    rw [hs]
    exact Nat.lt_floor_add_one _
  have h3 : 1 ≤ sCol n k := by
    rw [hs]
    apply Nat.floor_pos.2
    rw [one_le_div hl]
    exact hβl.le
  have hsR : (0 : ℝ) < sCol n k := by exact_mod_cast h3
  refine ⟨?_, h3, ?_⟩
  · rw [← hβ]
    rwa [le_div_iff₀ hl] at h1
  · rw [div_lt_iff₀ hl] at h2
    rw [div_le_div_iff₀ hsR (by linarith)]
    have : eCol n - (cCol k : ℝ) / 1000 ≤ β - lr k := by rw [hβ]; linarith
    nlinarith


/-- The arithmetic of the slots. -/
theorem slot_arith {Y t g s W : ℝ} (ht : 64 ≤ t) (hg2 : g ≤ 2048) (hY0 : 0 < Y)
    (hYg : Y * g ≤ W) (hW : 4096 ≤ W) (hs3 : s * 1964 ≤ (t - 18) * g) :
    (Y * (0.6932 * t + 1) + 2) * s * 16 * 1964 ≤ 16 * (W * (0.6932 * t ^ 2)) := by
  obtain ⟨A, hA⟩ : ∃ A, A = 0.6932 * t := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have h1 : (Y * g) * (A + 1) ≤ W * (A + 1) := mul_le_mul_of_nonneg_right hYg (by linarith)
  have h2 : (Y * (A + 1) + 2) * g ≤ W * (A + 2) := by
    have e1 : (Y * (A + 1) + 2) * g = (Y * g) * (A + 1) + 2 * g := by ring
    have e2 : W * (A + 2) = W * (A + 1) + W := by ring
    rw [e1, e2]
    linarith
  have hB : (t - 18) * (A + 2) ≤ 0.6932 * t ^ 2 := by
    rw [hA]
    nlinarith
  have hW0 : 0 ≤ W := by linarith
  have hYY : 0 ≤ Y * (A + 1) + 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs3 hYY
  have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ t - 18)
  have h5 := mul_le_mul_of_nonneg_left hB hW0
  calc (Y * (A + 1) + 2) * s * 16 * 1964 = 16 * ((Y * (A + 1) + 2) * (s * 1964)) := by ring
    _ ≤ 16 * ((Y * (A + 1) + 2) * ((t - 18) * g)) := by linarith
    _ = 16 * ((t - 18) * ((Y * (A + 1) + 2) * g)) := by ring
    _ ≤ 16 * ((t - 18) * (W * (A + 2))) := by linarith
    _ = 16 * (W * ((t - 18) * (A + 2))) := by ring
    _ ≤ _ := by linarith

/-- **The slots.** -/
theorem slot_col {n : ℕ} {k : ℕ × ℕ} (hk : KeyColReal k) (hE : (cCol k : ℝ) / 1000 < eCol n)
    (ht : 64 ≤ lg₂ n) (hlgt : 6 ≤ lg₂ (lg₂ n)) (hN : 64 * (lg₂ n) ^ 3 ≤ n) :
    tCol n k * (2 * sCol n k * 8) ≤ cslotCol n := by
  obtain ⟨hs1, hs2, -⟩ := sCol_facts hk hE
  have hkm : 0 < lr k := by linarith [hk.one_le]
  have hrate := hk.rate
  have hg1 := hk.g1
  have hg2 := hk.g2
  have hlg0 : 0 ≤ lg₂ ((gCol k : ℝ) / 64) := Real.logb_nonneg (by norm_num) hg1
  have hβ : eCol n - lg₂ ((gCol k : ℝ) / 64) ≤ lg₂ n - 18 := by
    rw [eCol]
    linarith
  obtain ⟨t, htdef⟩ : ∃ t, t = lg₂ (n : ℝ) := ⟨_, rfl⟩
  rw [← htdef] at ht hN hβ
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = (gCol k : ℝ) := ⟨_, rfl⟩
  rw [← hgdef] at hg1 hg2 hrate hs1 hβ hlg0
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (sCol n k : ℝ) := ⟨_, rfl⟩
  rw [← hsdef] at hs1
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have ht0 : 0 < t := by linarith
  have hg0 : 0 < g := by linarith
  have hN0 : (0 : ℝ) < n := by
    have : 0 < 64 * t ^ 3 := by positivity
    linarith
  -- `2 ≤ m / w`, so the ratio is positive
  have hρ : (0 : ℝ) < (k.1 : ℝ) / k.2 := by
    by_contra hcon
    have h0 : lr k = Real.logb 2 ((k.1 : ℝ) / k.2) := rfl
    have hle : (k.1 : ℝ) / k.2 ≤ 0 := not_lt.1 hcon
    have hnn : (0 : ℝ) ≤ (k.1 : ℝ) / k.2 := by positivity
    have h00 : (k.1 : ℝ) / k.2 = 0 := le_antisymm hle hnn
    rw [h00, Real.logb_zero] at h0
    linarith
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = ((k.1 : ℝ) / k.2) ^ sCol n k := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hYdef]; positivity
  -- `Y ≤ n / (t³ (g / 64))`
  have hY : Y ≤ (n : ℝ) / (t ^ 3 * (g / 64)) := by
    have h1 : lg₂ Y ≤ lg₂ ((n : ℝ) / (t ^ 3 * (g / 64))) := by
      rw [hYdef, Real.logb_pow, Real.logb_div hN0.ne' (by positivity),
        Real.logb_mul (by positivity) (by positivity), Real.logb_pow, ← htdef]
      have h2 : ((sCol n k : ℕ) : ℝ) * lg₂ ((k.1 : ℝ) / k.2) = s * lr k := by rw [hsdef]; rfl
      rw [h2]
      have h3 : eCol n = t - 3 * lg₂ t := by rw [eCol, ← htdef]
      rw [h3] at hs1
      push_cast
      linarith
    exact (Real.logb_le_logb (by norm_num) hY0 (by positivity)).1 h1
  have hYg : Y * g ≤ 64 * (n : ℝ) / t ^ 3 := by
    have e : 64 * (n : ℝ) / t ^ 3 = (n : ℝ) / (t ^ 3 * (g / 64)) * g := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hY hg0.le
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = 64 * (n : ℝ) / t ^ 3 := ⟨_, rfl⟩
  rw [← hWdef] at hYg
  have hW : 4096 ≤ W := by
    rw [hWdef, le_div_iff₀ (by positivity)]
    linarith
  have hlog : Real.log (n : ℝ) ≤ 0.6932 * t := by
    have h1 : Real.log (n : ℝ) = t * Real.log 2 := by
      rw [htdef, Real.logb, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
    have h2 := Real.log_two_lt_d9
    rw [h1]
    nlinarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hT : ((tCol n k : ℕ) : ℝ) ≤ Y * (0.6932 * t + 1) + 2 := by
    have h1 := Nat.ceil_lt_add_one (a := ((k.1 : ℝ) / k.2) ^ sCol n k * (Real.log (n : ℝ) + 1) + 1)
      (by positivity)
    have h2 : Y * (Real.log (n : ℝ) + 1) ≤ Y * (0.6932 * t + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hY0.le
    simp only [tCol]
    rw [← hYdef] at h1 ⊢
    linarith
  have hs3 : s * 1964 ≤ (t - 18) * g := by
    have h1 : s * 1964 ≤ s * (g * lr k) := mul_le_mul_of_nonneg_left hrate hs0
    have h2 : g * (s * lr k) ≤ g * (t - 18) := mul_le_mul_of_nonneg_left (by linarith) hg0.le
    have e1 : s * (g * lr k) = g * (s * lr k) := by ring
    have e2 : g * (t - 18) = (t - 18) * g := by ring
    linarith
  have hfin := slot_arith ht hg2 hY0 hYg hW hs3
  have hWt : W * t ^ 2 = 64 * (n : ℝ) / t := by
    rw [hWdef]
    field_simp
  apply Nat.le_floor
  push_cast
  rw [← htdef, ← hsdef]
  have h5 : ((tCol n k : ℕ) : ℝ) * (2 * s * 8) ≤ (Y * (0.6932 * t + 1) + 2) * (2 * s * 8) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have e2 : (16 * 0.6932 * 64 / 1964 : ℝ) * n / t = 16 * (W * (0.6932 * t ^ 2)) / 1964 := by
    have : W * (0.6932 * t ^ 2) = 0.6932 * (W * t ^ 2) := by ring
    rw [this, hWt]
    ring
  have e3 : (Y * (0.6932 * t + 1) + 2) * (2 * s * 8) = (Y * (0.6932 * t + 1) + 2) * s * 16 := by ring
  rw [e2, le_div_iff₀ (by norm_num)]
  rw [e3] at h5
  linarith

/-! ### The number of rounds -/

theorem rounds_col (ms : List (ℕ × ℕ)) (n x : ℕ) (hx : 0 < x)
    (h : ∀ k ∈ ms, 1 ≤ sCol n k ∧ sCol n k ≤ x ∧ 1 / (sCol n k : ℝ) ≤ lr k / (eCol n - (cCol k : ℝ) / 1000)) :
    (colRounds (2 * x ^ 4) (sCol n) ms : ℝ) ≤
      (x : ℝ) ^ 4 * (1 + 1 / (x : ℝ) ^ 3) * (ms.map fun k => lr k / (eCol n - (cCol k : ℝ) / 1000)).sum := by
  induction ms with
  | nil => simp [colRounds]
  | cons a t ih =>
    have ih' := ih fun k hk => h k (List.mem_cons_of_mem _ hk)
    obtain ⟨h1, h2, h3⟩ := h a List.mem_cons_self
    have hc := piece_chunks x (sCol n a) h1 h2
    simp only [colRounds, List.map_cons, List.sum_cons] at ih' ⊢
    rw [Nat.cast_add, mul_add]
    refine add_le_add ?_ ih'
    refine hc.trans ?_
    have e : (x : ℝ) ^ 4 / (sCol n a : ℝ) * (1 + 1 / (x : ℝ) ^ 3) =
        (x : ℝ) ^ 4 * (1 + 1 / (x : ℝ) ^ 3) * (1 / (sCol n a : ℝ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### Averaging -/

theorem lg_term {m w P : ℕ} (p q : ℕ) (hm : 0 < m) (hw : 0 < w) (hP : 0 < P) :
    lg₂ ((m ^ p * w ^ q * P : ℕ) : ℝ) = (p : ℝ) * lg₂ (m : ℝ) + (q : ℝ) * lg₂ (w : ℝ) + lg₂ (P : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  push_cast
  rw [Real.logb_mul (by positivity) hP'.ne', Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_pow]

/-- The weighted sum of the constants, as the logarithm of a ratio of products. -/
theorem weighted_eq (ms : List (ℕ × ℕ)) (c : ℕ × ℕ → ℕ) (c₀ : ℕ) (h : ∀ k ∈ ms, 0 < k.1 ∧ 0 < k.2) :
    (ms.map fun k => lr k * ((c k : ℝ) / 1000 - (c₀ : ℝ) / 1000)).sum =
      (lg₂ (((ms.map fun k => k.1 ^ c k * k.2 ^ c₀).prod : ℕ) : ℝ) -
        lg₂ (((ms.map fun k => k.1 ^ c₀ * k.2 ^ c k).prod : ℕ) : ℝ)) / 1000 ∧
      0 < (ms.map fun k => k.1 ^ c k * k.2 ^ c₀).prod ∧ 0 < (ms.map fun k => k.1 ^ c₀ * k.2 ^ c k).prod := by
  induction ms with
  | nil => simp
  | cons a t ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih fun k hk => h k (List.mem_cons_of_mem _ hk)
    obtain ⟨ha1, ha2⟩ := h a List.mem_cons_self
    have ha1' : (0 : ℝ) < a.1 := by exact_mod_cast ha1
    have ha2' : (0 : ℝ) < a.2 := by exact_mod_cast ha2
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    refine ⟨?_, by positivity, by positivity⟩
    rw [ih1, lg_term _ _ ha1 ha2 ih2, lg_term _ _ ha1 ha2 ih3]
    simp only [lr]
    rw [Real.logb_div ha1'.ne' ha2'.ne']
    ring

theorem weighted_col (ms : List (ℕ × ℕ)) (c : ℕ × ℕ → ℕ) (c₀ : ℕ) (h : ∀ k ∈ ms, 0 < k.1 ∧ 0 < k.2)
    (hp : (ms.map fun k => k.1 ^ c k * k.2 ^ c₀).prod ≤ (ms.map fun k => k.1 ^ c₀ * k.2 ^ c k).prod) :
    (ms.map fun k => lr k * ((c k : ℝ) / 1000 - (c₀ : ℝ) / 1000)).sum ≤ 0 := by
  obtain ⟨h1, h2, -⟩ := weighted_eq ms c c₀ h
  rw [h1]
  have hr : (((ms.map fun k => k.1 ^ c k * k.2 ^ c₀).prod : ℕ) : ℝ) ≤
      (((ms.map fun k => k.1 ^ c₀ * k.2 ^ c k).prod : ℕ) : ℝ) := by exact_mod_cast hp
  have h3 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast h2) hr
  apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
  linarith

/-! ### The real inequality -/

/-- `log₂` of a ratio, by the tangent. -/
theorem lg_ratio_le {k t : ℝ} (hk : 0 < k) (ht : k ≤ t) : k * lg₂ (t / k) ≤ 1.45 * (t - k) := by
  have hq : 0 < t / k := div_pos (by linarith) hk
  have h1 : Real.log (t / k) ≤ t / k - 1 := Real.log_le_sub_one_of_pos hq
  have hq1 : 0 ≤ t / k - 1 := by
    have : 1 ≤ t / k := by
      rw [le_div_iff₀ hk]
      linarith
    linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h2 : lg₂ (t / k) ≤ 1.45 * (t / k - 1) := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have e : k * (t / k - 1) = t - k := by
    field_simp
  calc k * lg₂ (t / k) ≤ k * (1.45 * (t / k - 1)) := mul_le_mul_of_nonneg_left h2 hk.le
    _ = 1.45 * (k * (t / k - 1)) := by ring
    _ = _ := by rw [e]

theorem lg_split {k t : ℝ} (hk : 0 < k) (ht : k ≤ t) : lg₂ t = lg₂ k + lg₂ (t / k) := by
  rw [← Real.logb_mul hk.ne' (div_pos (by linarith) hk).ne']
  congr 1
  field_simp

/-- `log₂ t` for `t ≥ 64`: the tangent at `64`. -/
theorem lg_tangent {t : ℝ} (ht : 64 ≤ t) : 6 ≤ lg₂ t ∧ 64 * (lg₂ t - 6) ≤ 1.45 * (t - 64) := by
  have hlg64 : lg₂ 64 = 6 := by
    have : (64 : ℝ) = 2 ^ 6 := by norm_num
    rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  constructor
  · have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) ht
    linarith
  · have h1 := lg_ratio_le (k := 64) (by norm_num) ht
    have h2 := lg_split (k := 64) (by norm_num) ht
    rw [hlg64] at h2
    have h3 : lg₂ t - 6 = lg₂ (t / 64) := by linarith
    rw [h3]
    exact h1

/-- The denominator is positive. -/
theorem denom_pos {t : ℝ} (ht : 64 ≤ t) : 0 < t - 3 * lg₂ t - 7.63 := by
  obtain ⟨-, h⟩ := lg_tangent ht
  linarith

/-- The real inequality for the sum of the error terms. -/
theorem final_real {E X t R : ℝ} (hX : 64 ≤ X) (hXt : X ≤ t) (htX : t ≤ X + 1) (hE1 : 0.6 * t ≤ E)
    (hE2 : E ≤ t - 24) (hR1 : 1 ≤ R) (hR2 : R ≤ 2) :
    (1 + 1 / X ^ 3) * (1 + R / t) * (1 / E + 1 ^ 2 / (E ^ 2 * (E - 1))) + 1 / (E ^ 2 * t) ≤ 1 / (E - R) := by
  have ht : 64 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hE0 : 38 ≤ E := by linarith
  have hE' : 0 < E := by linarith
  have hE1' : 0 < E - 1 := by linarith
  have hER : 0 < E - R := by linarith
  have hX0 : 0 < X := by linarith
  -- notation
  obtain ⟨ι, hι⟩ : ∃ ι, ι = 1 / (E * t) := ⟨_, rfl⟩
  have hι0 : 0 < ι := by rw [hι]; positivity
  have hι1 : ι ≤ 1 / 2400 := by
    rw [hι]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = 1 / E := ⟨_, rfl⟩
  have hΦ0 : 0 < Φ := by rw [hΦ]; positivity
  have a1 : 1 / X ^ 3 ≤ ι := by
    rw [hι]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : E * t ≤ t * t := mul_le_mul_of_nonneg_right (by linarith) ht0.le
    have h2 : t * t ≤ (X + 1) * (X + 1) := mul_le_mul htX htX ht0.le (by linarith)
    have h3 : (X + 1) * (X + 1) ≤ X ^ 3 := by nlinarith
    linarith
  have a2 : 1 ^ 2 / (E ^ 2 * (E - 1)) ≤ 2 * Φ * ι := by
    have e : 2 * Φ * ι = 2 / (E ^ 2 * t) := by
      rw [hΦ, hι]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : t ≤ 2 * (E - 1) := by linarith
    have h2 : 0 < E ^ 2 := by positivity
    nlinarith
  have a3 : (1 : ℝ) / (E ^ 2 * t) = Φ * ι := by
    rw [hΦ, hι]
    field_simp
  have a4 : (1 + R / t) * Φ + 6 * (Φ * ι) ≤ 1 / (E - R) := by
    have e : (1 + R / t) * Φ + 6 * (Φ * ι) = (E * (t + R) + 6) / (E ^ 2 * t) := by
      rw [hΦ, hι]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) hER]
    have h1 : R * (E - t - R) + 6 ≤ 0 := by nlinarith
    have h2 : E * (R * (E - t - R) + 6) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hE'.le h1
    nlinarith
  rw [a3]
  have hRt0 : 0 < R / t := by positivity
  have hRt : R / t ≤ 1 / 32 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]
    linarith
  have hA : 0 ≤ 1 / X ^ 3 := by positivity
  have hB : 0 ≤ 1 ^ 2 / (E ^ 2 * (E - 1)) := by positivity
  have hs1 : (1 + 1 / X ^ 3) * (1 + R / t) * (1 / E + 1 ^ 2 / (E ^ 2 * (E - 1))) ≤
      (1 + ι) * (1 + R / t) * (Φ + 2 * Φ * ι) := by
    rw [← hΦ]
    apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hs2 : (1 + ι) * (1 + R / t) * (Φ + 2 * Φ * ι) ≤ (1 + R / t) * Φ + 5 * (Φ * ι) := by
    have h1 : (1 + ι) * (1 + 2 * ι) ≤ 1 + 4 * ι := by nlinarith
    have h2 : (1 + R / t) * Φ * ((1 + ι) * (1 + 2 * ι)) ≤ (1 + R / t) * Φ * (1 + 4 * ι) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 0 ≤ Φ * ι := by positivity
    have h4 : (R / t) * (Φ * ι) ≤ (1 / 32) * (Φ * ι) := mul_le_mul_of_nonneg_right hRt h3
    nlinarith
  linarith

/-! ### The word length -/

theorem poly_col (x : ℕ) (hx : 64 ≤ x) : 2 ^ 16 * x ^ 8 ≤ 2 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    have h1 : 64 * (x + 1) ≤ 65 * x := by omega
    have h2 : (64 * (x + 1)) ^ 8 ≤ (65 * x) ^ 8 := Nat.pow_le_pow_left h1 8
    have h3 : (x + 1) ^ 8 ≤ 2 * x ^ 8 := by
      rw [mul_pow, mul_pow] at h2
      refine Nat.le_of_mul_le_mul_left (c := 64 ^ 8) (h2.trans ?_) (by norm_num)
      have e : 64 ^ 8 * (2 * x ^ 8) = (64 ^ 8 * 2) * x ^ 8 := by ring
      rw [e]
      exact Nat.mul_le_mul_right _ (by norm_num)
    rw [pow_succ 2 x]
    calc 2 ^ 16 * (x + 1) ^ 8 ≤ 2 ^ 16 * (2 * x ^ 8) := Nat.mul_le_mul_left _ h3
      _ = 2 ^ 16 * x ^ 8 * 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ ih

/-- The lower-order term of the word length. -/
theorem base_col {N X t E Λ : ℝ} {r : ℝ} (hX : 64 ≤ X) (ht0 : 0 < t) (htX : t ≤ 1.02 * X) (hE0 : 0 < E) (hEt : E ≤ t)
    (hΛ : 100 ≤ Λ) (hr : r ≤ N / 2) (hN : 400 * X ^ 7 ≤ N) :
    3 * N + 406 + 2200 * (r * (2 * X ^ 4 + 2)) ≤ Λ / 8 * N ^ 2 * (1 / (E ^ 2 * t)) := by
  have hX0 : 0 < X := by linarith
  have hX4 : 2204 ≤ X ^ 4 := by
    have : (64 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
    linarith
  have hX7 : X ≤ X ^ 7 := le_self_pow₀ (by linarith) (by norm_num)
  have hN1 : 25600 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hb : 3 * N + 406 + 2200 * (r * (2 * X ^ 4 + 2)) ≤ 2201 * X ^ 4 * N := by
    have h1 : r * (2 * X ^ 4 + 2) ≤ N / 2 * (2 * X ^ 4 + 2) := mul_le_mul_of_nonneg_right hr (by positivity)
    have h2 : 2204 * N ≤ X ^ 4 * N := mul_le_mul_of_nonneg_right hX4 hN0.le
    have h3 : 406 ≤ N + 6 := by linarith
    have e : N / 2 * (2 * X ^ 4 + 2) = X ^ 4 * N + N := by ring
    have e2 : 2201 * X ^ 4 * N = 2200 * (X ^ 4 * N) + X ^ 4 * N := by ring
    linarith
  have hE3 : E ^ 2 * t ≤ 2 * X ^ 3 := by
    have h1 : E ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hE0.le hEt 2
    have h2 : E ^ 2 * t ≤ t ^ 2 * t := mul_le_mul_of_nonneg_right h1 ht0.le
    have h3 : t ^ 3 ≤ (1.02 * X) ^ 3 := pow_le_pow_left₀ ht0.le htX 3
    have e : (1.02 * X) ^ 3 = 1.061208 * X ^ 3 := by ring
    have h4 : 0 < X ^ 3 := by positivity
    nlinarith
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have hbase0 : 0 ≤ 2201 * X ^ 4 * N := by positivity
  have h1 : (3 * N + 406 + 2200 * (r * (2 * X ^ 4 + 2))) * (E ^ 2 * t) ≤ (2201 * X ^ 4 * N) * (2 * X ^ 3) :=
    mul_le_mul hb hE3 (by positivity) hbase0
  have h2 : (2201 * X ^ 4 * N) * (2 * X ^ 3) = 4402 * N * X ^ 7 := by ring
  have h3 : 4402 * N * X ^ 7 ≤ (100 / 8) * N * N := by
    have : N * (4402 * X ^ 7) ≤ N * ((100 / 8) * N) := mul_le_mul_of_nonneg_left (by linarith) hN0.le
    linarith
  have h4 : (100 / 8) * N * N ≤ Λ / 8 * N ^ 2 := by
    have : 0 ≤ N ^ 2 := by positivity
    have e : (100 / 8) * N * N = (100 / 8) * N ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) this
  linarith

/-- One pass of the bracket. -/
theorem bracket_col {N X t A₁ A₂ C : ℝ} (hN : 0 < N) (hX : 0 < X) (ht : 0 < t) (hA₁ : A₁ ≤ N ^ 2 / (8 * X ^ 4))
    (hA₂ : A₂ + 1 ≤ N / (4 * X ^ 4) + 1) (hC0 : 0 ≤ C)
    (hC : C ≤ (16 * 0.6932 * 64 / 1964 : ℝ) * N / t) (hX4 : 40000 * X ^ 4 ≤ N) :
    A₁ + 2 * (A₂ + 1) * C ≤ N ^ 2 / (8 * X ^ 4) * (1 + 1.447 / t) := by
  have h1 : 2 * (A₂ + 1) * C ≤ 2 * (N / (4 * X ^ 4) + 1) * ((16 * 0.6932 * 64 / 1964 : ℝ) * N / t) :=
    mul_le_mul (by linarith) hC hC0 (by positivity)
  have h2 : 2 * (N / (4 * X ^ 4) + 1) * ((16 * 0.6932 * 64 / 1964 : ℝ) * N / t) =
      N ^ 2 / (8 * X ^ 4) * ((16 * 0.6932 * 64 / 1964 : ℝ) * (4 + 16 * X ^ 4 / N) / t) := by
    field_simp
    ring
  have h3 : 16 * X ^ 4 / N ≤ 1 / 2500 := by
    rw [div_le_div_iff₀ hN (by norm_num)]
    linarith
  have h4 : (16 * 0.6932 * 64 / 1964 : ℝ) * (4 + 16 * X ^ 4 / N) / t ≤ 1.447 / t := by
    apply div_le_div_of_nonneg_right _ ht.le
    have hp : 0 ≤ 16 * X ^ 4 / N := by positivity
    norm_num at h3 ⊢
    linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ N ^ 2 / (8 * X ^ 4))
  rw [mul_add, mul_one]
  linarith

/-- **The second-order bound of the word length.** -/
theorem colouredW_second (ms : List (ℕ × ℕ)) (hok : ∀ k ∈ ms, keyColOK k)
    (hp : (ms.map fun k => k.1 ^ cCol k * k.2 ^ 6183).prod ≤ (ms.map fun k => k.1 ^ 6183 * k.2 ^ cCol k).prod)
    (hΛ : 100 ≤ sumRatio ms) {n : ℕ} (hx64 : 64 ≤ Nat.log 2 n) :
    ParamsOK n 8 (cslotCol n) (sCol n) (tCol n) ms ∧
    (colouredW n (2 * (Nat.log 2 n) ^ 4) (cslotCol n) (sCol n) ms : ℝ) ≤
      sumRatio ms / 8 * (n : ℝ) ^ 2 / (lg₂ n - 3 * lg₂ (lg₂ n) - 7.63) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hx64
  obtain ⟨hl1, hl2⟩ := logb_bounds hn0
  obtain ⟨x, hxdef⟩ : ∃ x, x = Nat.log 2 n := ⟨_, rfl⟩
  rw [← hxdef] at hx64 hl1 hl2 ⊢
  have hxn : 2 ^ x ≤ n := by
    rw [hxdef]
    exact Nat.pow_log_le_self 2 hn0
  have hpoly := poly_col x hx64
  have hX : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  have hX0 : (0 : ℝ) < x := by linarith
  have hN0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hN : (65536 : ℝ) * (x : ℝ) ^ 8 ≤ n := by exact_mod_cast hpoly.trans hxn
  have hpw : ∀ (A : ℝ) (j : ℕ), 0 ≤ A → A ≤ 65536 → j ≤ 8 → A * (x : ℝ) ^ j ≤ n := by
    intro A j hA0 hA hj
    have h1 : (x : ℝ) ^ j ≤ (x : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) hj
    have h2 : A * (x : ℝ) ^ j ≤ 65536 * (x : ℝ) ^ 8 :=
      mul_le_mul hA h1 (by positivity) (by norm_num)
    linarith
  obtain ⟨t, htdef⟩ : ∃ t, t = lg₂ (n : ℝ) := ⟨_, rfl⟩
  rw [← htdef] at hl1 hl2 ⊢
  have ht : 64 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have ht102 : t ≤ 1.02 * (x : ℝ) := by linarith
  obtain ⟨hlgt, hlgt2⟩ := lg_tangent ht
  obtain ⟨E, hEdef⟩ : ∃ E, E = eCol n := ⟨_, rfl⟩
  have hEe : E = t - 3 * lg₂ t := by rw [hEdef, eCol, ← htdef]
  have hE' : 0.6 * t ≤ E - 6.183 := by rw [hEe]; linarith
  have hE'' : E - 6.183 ≤ t - 24 := by rw [hEe]; linarith
  have ht3 : 64 * t ^ 3 ≤ n := by
    have h3 : t ^ 3 ≤ (1.02 * (x : ℝ)) ^ 3 := pow_le_pow_left₀ ht0.le ht102 3
    have e : (1.02 * (x : ℝ)) ^ 3 = 1.061208 * (x : ℝ) ^ 3 := by ring
    have h4 := hpw 128 3 (by norm_num) (by norm_num) (by norm_num)
    have h5 : 0 < (x : ℝ) ^ 3 := by positivity
    nlinarith
  have hfacts : ∀ k ∈ ms, 1 ≤ sCol n k ∧ sCol n k ≤ x ∧
      1 / (sCol n k : ℝ) ≤ lr k / (E - (cCol k : ℝ) / 1000) := by
    intro k hk
    have hkr := keyColReal_of_ok (hok k hk)
    have hc := hkr.c2
    have hEc : (cCol k : ℝ) / 1000 < eCol n := by
      rw [← hEdef]
      linarith
    obtain ⟨h1, h2, h3⟩ := sCol_facts hkr hEc
    rw [← hEdef] at h1 h3
    refine ⟨h2, ?_, h3⟩
    have hg := Real.logb_nonneg (b := 2) (by norm_num) hkr.g1
    have hs0 : (0 : ℝ) ≤ sCol n k := by positivity
    have h4 : (sCol n k : ℝ) ≤ (sCol n k : ℝ) * lr k := le_mul_of_one_le_right hs0 hkr.one_le
    have h5 : (sCol n k : ℝ) ≤ x := by
      rw [hEe] at h1
      linarith
    exact_mod_cast h5
  have hparams : ParamsOK n 8 (cslotCol n) (sCol n) (tCol n) ms := by
    refine ⟨fun k hk => (hfacts k hk).1, fun k _ => Nat.le_ceil _, fun k hk => ?_⟩
    have hkr := keyColReal_of_ok (hok k hk)
    have hc := hkr.c2
    refine slot_col hkr (by rw [← hEdef]; linarith) (by rw [← htdef]; exact ht)
      (by rw [← htdef]; exact hlgt) (by rw [← htdef]; exact ht3)
  refine ⟨hparams, ?_⟩
  -- the sum over the keys
  obtain ⟨E₁, hE₁⟩ : ∃ E₁, E₁ = E - 6.183 := ⟨_, rfl⟩
  rw [← hE₁] at hE' hE''
  have hE₁0 : 38 ≤ E₁ := by linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = sumRatio ms := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 / E₁ + 1 ^ 2 / (E₁ ^ 2 * (E₁ - 1)) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    have : 0 < E₁ - 1 := by linarith
    positivity
  have hsum : (ms.map fun k => lr k / (E - (cCol k : ℝ) / 1000)).sum ≤ Λ * Q := by
    have h1 := sum_div_le ms lr (fun k => (cCol k : ℝ) / 1000 - ((6183 : ℕ) : ℝ) / 1000) E₁ 1
      (by linarith) (by norm_num)
      (fun k hk => by linarith [(keyColReal_of_ok (hok k hk)).one_le])
      (fun k hk => by
        have hkr := keyColReal_of_ok (hok k hk)
        have a := hkr.c1
        have b := hkr.c2
        rw [abs_le]
        norm_num
        constructor <;> linarith)
    have h2 := weighted_col ms cCol 6183 (fun k hk => by
      obtain ⟨h0, h2, -⟩ := hok k hk
      exact ⟨by omega, h0⟩) hp
    have e1 : (ms.map fun k => lr k / (E - (cCol k : ℝ) / 1000)) =
        ms.map fun k => lr k / (E₁ - ((cCol k : ℝ) / 1000 - ((6183 : ℕ) : ℝ) / 1000)) := by
      apply List.map_congr_left
      intro k _
      congr 1
      rw [hE₁]
      push_cast
      ring
    rw [e1]
    refine h1.trans ?_
    have h3 : (ms.map fun k => lr k * ((cCol k : ℝ) / 1000 - ((6183 : ℕ) : ℝ) / 1000)).sum * (1 / E₁ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h2 (by positivity)
    have h4 : (ms.map lr).sum = Λ := by rw [hΛdef]; rfl
    rw [h4, ← hQ]
    linarith
  have hrounds := rounds_col ms n x (by omega) (by rw [← hEdef]; exact hfacts)
  rw [← hEdef] at hrounds
  have hX3 : (0 : ℝ) ≤ (x : ℝ) ^ 4 * (1 + 1 / (x : ℝ) ^ 3) := by positivity
  have hR2 : (colRounds (2 * x ^ 4) (sCol n) ms : ℝ) ≤ (x : ℝ) ^ 4 * (1 + 1 / (x : ℝ) ^ 3) * (Λ * Q) :=
    hrounds.trans (mul_le_mul_of_nonneg_left hsum hX3)
  -- the bracket
  obtain ⟨r, hr⟩ : ∃ r, r = n / 2 - 1 := ⟨_, rfl⟩
  have h2r : 2 * r ≤ n := by omega
  obtain ⟨p2, p3⟩ := piece_cols n x r h2r (by omega)
  have hCs : (cslotCol n : ℝ) ≤ (16 * 0.6932 * 64 / 1964 : ℝ) * n / t := by
    rw [htdef, cslotCol]
    apply Nat.floor_le
    rw [← htdef]
    positivity
  have hbr := bracket_col (A₁ := ((r ^ 2 / (2 * x ^ 4) : ℕ) : ℝ)) (A₂ := ((r / (2 * x ^ 4) : ℕ) : ℝ))
    (C := (cslotCol n : ℝ)) hN0 hX0 ht0 p2 p3 (by positivity) hCs
    (hpw 40000 4 (by norm_num) (by norm_num) (by norm_num))
  have hrR : (r : ℝ) ≤ (n : ℝ) / 2 := by
    have h : (2 : ℝ) * r ≤ n := by exact_mod_cast h2r
    linarith
  have hb := base_col (N := (n : ℝ)) (X := (x : ℝ)) (t := t) (E := E₁) (Λ := Λ) (r := (r : ℝ)) hX ht0 ht102
    (by linarith) (by linarith) hΛ hrR (hpw 400 7 (by norm_num) (by norm_num) (by norm_num))
  have hfin := final_real (E := E₁) (X := (x : ℝ)) (t := t) (R := 1.447) hX hl1 hl2.le hE' hE'' (by norm_num)
    (by norm_num)
  rw [← hQ] at hfin
  have hdef : (colouredW n (2 * x ^ 4) (cslotCol n) (sCol n) ms : ℝ) =
      3 * n + 406 + 2200 * ((r : ℝ) * (2 * (x : ℝ) ^ 4 + 2)) +
        (colRounds (2 * x ^ 4) (sCol n) ms : ℝ) *
          (((r ^ 2 / (2 * x ^ 4) : ℕ) : ℝ) + 2 * (((r / (2 * x ^ 4) : ℕ) : ℝ) + 1) * (cslotCol n : ℝ)) := by
    simp only [colouredW, ← hr]
    push_cast
    ring
  rw [hdef]
  have hΛ0 : 0 ≤ Λ := by linarith
  have hE₁t : t - 3 * lg₂ t - 7.63 = E₁ - 1.447 := by
    rw [hE₁, hEe]
    ring
  rw [hE₁t]
  have hbr0 : (0 : ℝ) ≤ ((r ^ 2 / (2 * x ^ 4) : ℕ) : ℝ) +
      2 * (((r / (2 * x ^ 4) : ℕ) : ℝ) + 1) * (cslotCol n : ℝ) := by positivity
  have hprod := mul_le_mul hR2 hbr hbr0 (by positivity)
  have e : (x : ℝ) ^ 4 * (1 + 1 / (x : ℝ) ^ 3) * (Λ * Q) * ((n : ℝ) ^ 2 / (8 * (x : ℝ) ^ 4) * (1 + 1.447 / t)) =
      Λ / 8 * (n : ℝ) ^ 2 * ((1 + 1 / (x : ℝ) ^ 3) * (1 + 1.447 / t) * Q) := by
    field_simp
  rw [e] at hprod
  have hK : 0 ≤ Λ / 8 * (n : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfin hK
  have e2 : Λ / 8 * (n : ℝ) ^ 2 * (1 / (E₁ - 1.447)) = Λ / 8 * (n : ℝ) ^ 2 / (E₁ - 1.447) := by ring
  rw [e2, mul_add] at hmul
  linarith

/-! ### God's number of the coloured cube -/

/-- `Z = 24! / 24⁶`. -/
abbrev ZCol : ℕ := Nat.factorial 24 / 24 ^ 6

theorem colKeys_ok : ∀ k ∈ colourData.keys, keyColOK k := by
  rw [colourData_keys]
  decide +kernel

theorem colKeys_prod : (colourData.keys.map fun k => k.1 ^ cCol k * k.2 ^ 6183).prod ≤
    (colourData.keys.map fun k => k.1 ^ 6183 * k.2 ^ cCol k).prod := by
  rw [colourData_keys]
  decide +kernel

theorem ZCol_pow_upper : ZCol ^ 10000 ≤ 2 ^ 515284 := by decide +kernel

theorem ZCol_pow_lower : 2 ^ 5000 ≤ ZCol ^ 100 := by decide +kernel

/-- `k ≤ log₂ n` when `2 ^ k ≤ n`. -/
theorem lg_of_two_pow_le {k n : ℕ} (hn : 2 ^ k ≤ n) : (k : ℝ) ≤ Real.logb 2 n := by
  have h1 : ((2 : ℝ) ^ k) ≤ n := by exact_mod_cast hn
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  exact h2

/-- `log₂ a ≤ p / q` from integers. -/
theorem logb_le_of_pow {a p q : ℕ} (ha : 0 < a) (hq : 0 < q) (h : a ^ q ≤ 2 ^ p) :
    lg₂ (a : ℝ) ≤ (p : ℝ) / q := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (a : ℝ) ^ q ≤ (2 : ℝ) ^ p := by exact_mod_cast h
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h3
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h5
  rw [le_div_iff₀ hq']
  linarith

/-- **`log₂(24!/24⁶) / 4 ≤ 12.8821`**, by a comparison of integers in the kernel. -/
theorem logZ_div_four_le : Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 ≤ (12.8821 : ℝ) := by
  have h := logb_le_of_pow (a := ZCol) (p := 515284) (q := 10000) (by decide +kernel) (by norm_num)
    ZCol_pow_upper
  have h1 : (((515284 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) = 51.5284 := by norm_num
  rw [h1] at h
  have e : Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) = lg₂ (ZCol : ℝ) := rfl
  rw [e]
  linarith

theorem lambda_colKeys : (100 : ℝ) ≤ sumRatio colourData.keys := by
  rw [sumRatio_colourData]
  have hZ : 0 < ZCol := by decide +kernel
  have hZ' : (0 : ℝ) < (ZCol : ℝ) := by exact_mod_cast hZ
  have h3 : (2 : ℝ) ^ 5000 ≤ (ZCol : ℝ) ^ 100 := by exact_mod_cast ZCol_pow_lower
  have h5 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h3
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h5
  have e : Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) = lg₂ (ZCol : ℝ) := rfl
  rw [e]
  push_cast at h5
  linarith

/-- **No `ε`: the second-order term for the coloured cube, for every `n ≥ 2 ^ 64`.** -/
theorem godColoured_second_order (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (godColoured μ n : ℝ) ≤ Real.logb 2 (Nat.factorial 24 / 24 ^ 6 : ℕ) / 4 * (n : ℝ) ^ 2 /
      (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := by
  have hx : 64 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have hn3 : 3 ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  obtain ⟨hp, hW⟩ := colouredW_second colourData.keys colKeys_ok colKeys_prod lambda_colKeys hx
  have hle := godColoured_le_colouredW μ hn3 colourData colourData_valid (2 * (Nat.log 2 n) ^ 4) (cslotCol n)
    (sCol n) (tCol n) (by have : 0 < Nat.log 2 n := by omega
                          positivity) (even_two_mul _) hp
  refine le_trans (by exact_mod_cast hle) (hW.trans (le_of_eq ?_))
  rw [sumRatio_colourData]
  ring

/-- **The same bound, with the number `12.8821`.** -/
theorem godColoured_second_order_num (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (godColoured μ n : ℝ) ≤ 12.8821 * (n : ℝ) ^ 2 / (Real.logb 2 n - 3 * Real.logb 2 (Real.logb 2 n) - 7.63) := by
  refine (godColoured_second_order μ hn).trans ?_
  have h := lg_of_two_pow_le (k := 64) hn
  have h0 := denom_pos (t := Real.logb 2 (n : ℝ)) (by push_cast at h; linarith)
  apply div_le_div_of_nonneg_right _ h0.le
  exact mul_le_mul_of_nonneg_right logZ_div_four_le (by positivity)

/-! ### Explicit bounds -/

/-- `t / (t - 3 log₂ t - 7.63)` decreases, in the form needed. -/
theorem ratio_col {t k : ℝ} (hk : 64 ≤ k) (ht : k ≤ t) :
    t * (k - 3 * lg₂ k - 7.63) ≤ k * (t - 3 * lg₂ t - 7.63) := by
  have hk0 : 0 < k := by linarith
  have h1 := lg_ratio_le hk0 ht
  have h2 := lg_split hk0 ht
  obtain ⟨h3, -⟩ := lg_tangent hk
  rw [h2]
  have h4 : 0 ≤ (t - k) * (3 * lg₂ k + 7.63 - 3 * 1.45) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- From the second-order bound to `C n² / log₂ n`, for `n ≥ 2 ^ k`, with `log₂ k ≤ a`. -/
theorem godColoured_explicit_large (μ : Metric) {k n : ℕ} {a C : ℝ} (hk : 64 ≤ k) (hn : 2 ^ k ≤ n)
    (ha : lg₂ (k : ℝ) ≤ a) (hd : 0 < (k : ℝ) - 3 * a - 7.63) (hC : 12.8821 * (k : ℝ) ≤ C * ((k : ℝ) - 3 * a - 7.63)) :
    (godColoured μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have hn64 : 2 ^ 64 ≤ n := (Nat.pow_le_pow_right (by norm_num) hk).trans hn
  have hmain := godColoured_second_order_num μ hn64
  have hkR : (64 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht : (k : ℝ) ≤ Real.logb 2 n := lg_of_two_pow_le hn
  obtain ⟨t, htdef⟩ : ∃ t, t = Real.logb 2 (n : ℝ) := ⟨_, rfl⟩
  rw [← htdef] at hmain ht ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (k : ℝ) := ⟨_, rfl⟩
  rw [← hK] at hd hC hkR ht ha
  have hK0 : 0 < K := by linarith
  have ht0 : 0 < t := by linarith
  have hr := ratio_col hkR ht
  have hf0 := denom_pos (t := t) (by linarith)
  have hC0 : 0 ≤ C := by
    by_contra hcon
    have : C * (K - 3 * a - 7.63) < 0 := mul_neg_of_neg_of_pos (not_le.1 hcon) hd
    nlinarith
  refine hmain.trans ?_
  rw [div_le_div_iff₀ hf0 ht0]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have h1 : t * (K - 3 * a - 7.63) ≤ K * (t - 3 * lg₂ t - 7.63) := by
    have : t * (K - 3 * a - 7.63) ≤ t * (K - 3 * lg₂ K - 7.63) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
    linarith
  have hkey : 12.8821 * t ≤ C * (t - 3 * lg₂ t - 7.63) := by
    have h2 : (12.8821 * K) * t ≤ (C * (K - 3 * a - 7.63)) * t := mul_le_mul_of_nonneg_right hC ht0.le
    have h3 : C * (t * (K - 3 * a - 7.63)) ≤ C * (K * (t - 3 * lg₂ t - 7.63)) := mul_le_mul_of_nonneg_left h1 hC0
    have h4 : K * (12.8821 * t) ≤ K * (C * (t - 3 * lg₂ t - 7.63)) := by
      calc K * (12.8821 * t) = (12.8821 * K) * t := by ring
        _ ≤ (C * (K - 3 * a - 7.63)) * t := h2
        _ = C * (t * (K - 3 * a - 7.63)) := by ring
        _ ≤ C * (K * (t - 3 * lg₂ t - 7.63)) := h3
        _ = _ := by ring
    exact le_of_mul_le_mul_left h4 hK0
  calc 12.8821 * (n : ℝ) ^ 2 * t = (n : ℝ) ^ 2 * (12.8821 * t) := by ring
    _ ≤ (n : ℝ) ^ 2 * (C * (t - 3 * lg₂ t - 7.63)) := mul_le_mul_of_nonneg_left hkey hn2
    _ = _ := by ring

/-- The explicit bound at a power of two, `k = 2 ^ a`. -/
theorem godColoured_explicit_pow (μ : Metric) {a n : ℕ} {C : ℝ} (ha : 6 ≤ a) (hn : 2 ^ (2 ^ a) ≤ n)
    (hd : 0 < (2 : ℝ) ^ a - 3 * a - 7.63) (hC : 12.8821 * (2 : ℝ) ^ a ≤ C * ((2 : ℝ) ^ a - 3 * a - 7.63)) :
    (godColoured μ n : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have h64 : 64 ≤ 2 ^ a := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hlg : lg₂ (((2 ^ a : ℕ) : ℝ)) ≤ (a : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  exact godColoured_explicit_large μ h64 hn hlg (by push_cast; exact hd) (by push_cast; exact hC)

/-- `n ≥ 2 ^ 64`: the constant `21.49`, against `24.8` for the cube group. -/
theorem coloured_explicit_64 (μ : Metric) {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (godColoured μ n : ℝ) ≤ 21.49 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godColoured_explicit_pow μ (a := 6) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-- `n ≥ 2 ^ 78`: the constant `19.51`, the limit for the cube group. -/
theorem coloured_explicit_78 (μ : Metric) {n : ℕ} (hn : 2 ^ 78 ≤ n) :
    (godColoured μ n : ℝ) ≤ 19.51 * (n : ℝ) ^ 2 / Real.logb 2 n := by
  have hlg : lg₂ ((78 : ℕ) : ℝ) ≤ 6.2855 := by
    have h := logb_le_of_pow (a := 78) (p := 62855) (q := 10000) (by norm_num) (by norm_num) (by decide +kernel)
    have e : (((62855 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) = 6.2855 := by norm_num
    rwa [e] at h
  exact godColoured_explicit_large μ (k := 78) (a := 6.2855) (by norm_num) hn hlg (by norm_num) (by norm_num)

/-- `n ≥ 2 ^ 128`: the constant `16.6`, against `22.1` for the cube group. -/
theorem coloured_explicit_128 (μ : Metric) {n : ℕ} (hn : 2 ^ 128 ≤ n) :
    (godColoured μ n : ℝ) ≤ 16.6 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godColoured_explicit_pow μ (a := 7) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-- `n ≥ 2 ^ 256`: the constant `14.7`, against `20.8` for the cube group. -/
theorem coloured_explicit_256 (μ : Metric) {n : ℕ} (hn : 2 ^ 256 ≤ n) :
    (godColoured μ n : ℝ) ≤ 14.7 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godColoured_explicit_pow μ (a := 8) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

set_option exponentiation.threshold 2000 in
/-- `n ≥ 2 ^ 1024`: the constant `13.38`, against `19.9` for the cube group. -/
theorem coloured_explicit_1024 (μ : Metric) {n : ℕ} (hn : 2 ^ 1024 ≤ n) :
    (godColoured μ n : ℝ) ≤ 13.38 * (n : ℝ) ^ 2 / Real.logb 2 n :=
  godColoured_explicit_pow μ (a := 10) (by norm_num) (by simpa using hn) (by norm_num) (by norm_num)

/-- **Explicit upper bounds for the coloured cube**: `godColoured μ n ≤ C n² / log₂ n` for `n ≥ N₀`. -/
theorem coloured_explicit (μ : Metric) (n : ℕ) :
    (2 ^ 64 ≤ n → (godColoured μ n : ℝ) ≤ 21.49 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 78 ≤ n → (godColoured μ n : ℝ) ≤ 19.51 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 128 ≤ n → (godColoured μ n : ℝ) ≤ 16.6 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 256 ≤ n → (godColoured μ n : ℝ) ≤ 14.7 * (n : ℝ) ^ 2 / Real.logb 2 n) ∧
    (2 ^ 1024 ≤ n → (godColoured μ n : ℝ) ≤ 13.38 * (n : ℝ) ^ 2 / Real.logb 2 n) :=
  ⟨coloured_explicit_64 μ, coloured_explicit_78 μ, coloured_explicit_128 μ, coloured_explicit_256 μ,
    coloured_explicit_1024 μ⟩

end RubiksGN
