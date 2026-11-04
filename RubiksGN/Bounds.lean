import RubiksGN.Lower

/-!
# God's number: definitions unwound, exact inequalities
-/

open Equiv

namespace RubiksGN

variable {n : ℕ}

theorem allows_of_isQ (μ : Metric) (m : Move n) (h : IsQ m) : μ.allows m := by
  cases μ
  · trivial
  · exact h

theorem labelledSolvable_upperW (μ : Metric) (hn : 3 ≤ n) (s : ℕ) (hs : 0 < s) :
    LabelledSolvable μ n (upperW n s) := by
  intro g hg
  obtain ⟨w, h1, h2, h3⟩ := solve hn s hs g hg
  exact ⟨w, fun m hm => allows_of_isQ μ m (h1 m hm), h2, h3⟩

theorem coloured_of_labelled {μ : Metric} {k : ℕ} (h : LabelledSolvable μ n k) :
    ColouredSolvable μ n k := by
  intro g hg
  obtain ⟨w, h1, h2, h3⟩ := h g hg
  refine ⟨w, h1, h2, ?_⟩
  rw [h3]
  intro q q' hf
  simpa [colouring] using hf

theorem htm_of_qtm_labelled {k : ℕ} (h : LabelledSolvable .qtm n k) : LabelledSolvable .htm n k := by
  intro g hg
  obtain ⟨w, _, h2, h3⟩ := h g hg
  exact ⟨w, fun _ _ => trivial, h2, h3⟩

theorem htm_of_qtm_coloured {k : ℕ} (h : ColouredSolvable .qtm n k) : ColouredSolvable .htm n k := by
  intro g hg
  obtain ⟨w, _, h2, h3⟩ := h g hg
  exact ⟨w, fun _ _ => trivial, h2, h3⟩

theorem labelled_spec (μ : Metric) (hn : 3 ≤ n) : LabelledSolvable μ n (godLabelled μ n) :=
  Nat.sInf_mem (s := {k | LabelledSolvable μ n k}) ⟨_, labelledSolvable_upperW μ hn 1 one_pos⟩

theorem coloured_spec (μ : Metric) (hn : 3 ≤ n) : ColouredSolvable μ n (godColoured μ n) :=
  Nat.sInf_mem (s := {k | ColouredSolvable μ n k})
    ⟨_, coloured_of_labelled (labelledSolvable_upperW μ hn 1 one_pos)⟩

/-- The coloured God's number is at most the labelled one. -/
theorem godColoured_le_godLabelled (μ : Metric) (hn : 3 ≤ n) : godColoured μ n ≤ godLabelled μ n :=
  Nat.sInf_le (coloured_of_labelled (labelled_spec μ hn))

/-- Half turns only help (labelled cube). -/
theorem godLabelled_htm_le_qtm (hn : 3 ≤ n) : godLabelled .htm n ≤ godLabelled .qtm n :=
  Nat.sInf_le (htm_of_qtm_labelled (labelled_spec .qtm hn))

/-- Half turns only help (coloured cube). -/
theorem godColoured_htm_le_qtm (hn : 3 ≤ n) : godColoured .htm n ≤ godColoured .qtm n :=
  Nat.sInf_le (htm_of_qtm_coloured (coloured_spec .qtm hn))

/-- **Upper bound, exact form.** For every block size `s`. -/
theorem godLabelled_le_upperW (μ : Metric) (hn : 3 ≤ n) (s : ℕ) (hs : 0 < s) :
    godLabelled μ n ≤ upperW n s :=
  Nat.sInf_le (labelledSolvable_upperW μ hn s hs)

/-- **Lower bound, exact form.** -/
theorem lower_count (μ : Metric) (hn : 3 ≤ n) :
    Zval ^ innerOrbits n ≤ 6 ^ 6 * (9 * n + 1) ^ godColoured μ n :=
  count_bound hn μ _ (coloured_spec μ hn)

end RubiksGN
