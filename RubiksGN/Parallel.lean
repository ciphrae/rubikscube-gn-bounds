import RubiksGN.Cover
import RubiksGN.Universal

/-!
# Performing a different even permutation on every orbit, in parallel

For each letter of the universal sequence, Lupanov's cover applies that letter to exactly the orbits
that need it, at a cost of about `2 |R| |C| / s` moves per letter.
-/

open Equiv

namespace RubiksGN

open Classical

variable {n : ℕ}

/-- The word applies its identity action to the corners, the middle edges and the face centres. -/
def FixesSkel (hn : 2 ≤ n) (w : Word n) : Prop :=
  (∀ (j : Fin n), (j = topI hn ∨ layerZ n j = 0) → ∀ k,
    Word.eval w (e (rep ⟨0, by omega⟩ j) k) = e (rep ⟨0, by omega⟩ j) k) ∧
  (∀ m : Fin n, layerZ n m = 0 → ∀ k, Word.eval w (e (rep m m) k) = e (rep m m) k)

theorem FixesSkel.nil (hn : 2 ≤ n) : FixesSkel hn ([] : Word n) :=
  ⟨fun _ _ _ => by simp, fun _ _ _ => by simp⟩

theorem FixesSkel.append {hn : 2 ≤ n} {u v : Word n} (hu : FixesSkel hn u) (hv : FixesSkel hn v) :
    FixesSkel hn (u ++ v) := by
  constructor
  · intro j hj k
    simp only [Word.eval_append, Perm.mul_apply]
    rw [hv.1 j hj k, hu.1 j hj k]
  · intro m hm k
    simp only [Word.eval_append, Perm.mul_apply]
    rw [hv.2 m hm k, hu.2 m hm k]

theorem row_col_dom (i j : Fin n) (hi : IsRow i) (hj : IsCol j) : InDom i j := by
  simp only [IsRow] at hi
  simp only [IsCol] at hj
  simp only [InDom, layerZ]
  omega

theorem gadget_fixesSkel (hn : 2 ≤ n) (L : Letter) (X Y : Finset (Fin n)) (hX : ∀ i ∈ X, IsRow i)
    (hY : ∀ j ∈ Y, IsCol j) : FixesSkel hn (gadgetW hn L X Y) := by
  constructor
  · intro j hj k
    apply gadget_off hn L X Y hX hY
    · refine ⟨?_, ?_⟩
      · simp only [layerZ]; omega
      · rcases hj with rfl | hj
        · simp only [layerZ, topI]; omega
        · omega
    · rintro ⟨h0, _⟩
      have := hX _ h0
      simp only [IsRow] at this
      omega
    · rintro ⟨_, _, i', hi', hle⟩
      have := hX _ hi'
      simp only [IsRow] at this
      rcases hj with rfl | hj
      · simp only [layerZ, topI] at hle; omega
      · rw [hj] at hle
        simp only [layerZ] at hle
        omega
  · intro m hm k
    exact gadget_center hn L X Y hX hY m hm k

/-- The word of one letter on a list of rectangles. -/
noncomputable def phaseW (hn : 2 ≤ n) (L : Letter) : List (Rect (Fin n) (Fin n)) → Word n
  | [] => []
  | r :: rs => gadgetW hn L r.1 r.2 ++ phaseW hn L rs

theorem phaseW_length (hn : 2 ≤ n) (L : Letter) (rs : List (Rect (Fin n) (Fin n))) :
    (phaseW hn L rs).length = (rs.map Rect.cost).sum := by
  induction rs with
  | nil => rfl
  | cons r t ih =>
    simp only [phaseW, List.length_append, ih, gadgetW_length, List.map_cons, List.sum_cons,
      Rect.cost]

theorem phaseW_isQ (hn : 2 ≤ n) (L : Letter) (rs : List (Rect (Fin n) (Fin n))) :
    ∀ m ∈ phaseW hn L rs, IsQ m := by
  induction rs with
  | nil => simp [phaseW]
  | cons r t ih =>
    intro m hm
    rcases List.mem_append.1 hm with h | h
    · exact gadgetW_isQ _ _ _ _ _ h
    · exact ih m h

variable {R C : Finset (Fin n)}

theorem phaseW_on (hn : 2 ≤ n) (L : Letter) (rs : List (Rect (Fin n) (Fin n)))
    (hX : ∀ r ∈ rs, ∀ i ∈ r.1, IsRow i) (hY : ∀ r ∈ rs, ∀ j ∈ r.2, IsCol j)
    (i j : Fin n) (hi : IsRow i) (hj : IsCol j) (k : Fin 24) :
    Word.eval (phaseW hn L rs) (e (rep i j) k) = e (rep i j) ((lp L ^ covers rs i j) k) := by
  induction rs generalizing k with
  | nil => simp [phaseW, covers]
  | cons r t ih =>
    have hXt : ∀ r ∈ t, ∀ i ∈ r.1, IsRow i := fun x hx => hX x (List.mem_cons_of_mem _ hx)
    have hYt : ∀ r ∈ t, ∀ j ∈ r.2, IsCol j := fun x hx => hY x (List.mem_cons_of_mem _ hx)
    have hXr := hX r List.mem_cons_self
    have hYr := hY r List.mem_cons_self
    simp only [phaseW, Word.eval_append, Perm.mul_apply]
    rw [ih hXt hYt]
    by_cases hin : i ∈ r.1 ∧ j ∈ r.2
    · rw [gadget_on hn L r.1 r.2 hXr hYr i j hin.1 hin.2]
      have : covers (r :: t) i j = covers t i j + 1 := by
        simp only [covers]
        rw [List.countP_cons_of_pos (by simpa using hin)]
      rw [this, pow_succ', Perm.mul_apply]
    · rw [gadget_off hn L r.1 r.2 hXr hYr i j (row_col_dom i j hi hj) hin (by
        rintro ⟨h0, _⟩
        simp only [IsRow] at hi
        omega)]
      have : covers (r :: t) i j = covers t i j := by
        simp only [covers]
        rw [List.countP_cons_of_neg (by simpa using hin)]
      rw [this]

theorem phaseW_fix (hn : 2 ≤ n) (L : Letter) (rs : List (Rect (Fin n) (Fin n)))
    (hX : ∀ r ∈ rs, ∀ i ∈ r.1, IsRow i) (hY : ∀ r ∈ rs, ∀ j ∈ r.2, IsCol j) :
    FixesSkel hn (phaseW hn L rs) := by
  induction rs with
  | nil => exact FixesSkel.nil hn
  | cons r t ih =>
    exact (gadget_fixesSkel hn L r.1 r.2 (hX r List.mem_cons_self) (hY r List.mem_cons_self)).append
      (ih (fun x hx => hX x (List.mem_cons_of_mem _ hx)) (fun x hx => hY x (List.mem_cons_of_mem _ hx)))

/-- The weight of one phase. -/
def phaseCost (r c s : ℕ) : ℕ := (r / s + 1) * ((2 * s + 4) * 2 ^ s + 2 * c)

/-- One letter on an arbitrary set of orbits. -/
theorem phase_exists (hn : 2 ≤ n) (L : Letter) (hR : ∀ i ∈ R, IsRow i) (hC : ∀ j ∈ C, IsCol j)
    (s : ℕ) (hs : 0 < s) (M : Fin n → Fin n → Prop) :
    ∃ w : Word n, (∀ m ∈ w, IsQ m) ∧ w.length ≤ phaseCost R.card C.card s ∧
      FixesSkel hn w ∧ ∀ i ∈ R, ∀ j ∈ C, ∀ k,
        Word.eval w (e (rep i j) k) = e (rep i j) (if M i j then lp L k else k) := by
  obtain ⟨rs, h1, h2, h3⟩ := lupanov s hs C M R
  have hX : ∀ r ∈ rs, ∀ i ∈ r.1, IsRow i := fun r hr i hi => hR i ((h1 r hr).1 hi)
  have hY : ∀ r ∈ rs, ∀ j ∈ r.2, IsCol j := fun r hr j hj => hC j ((h1 r hr).2 hj)
  refine ⟨phaseW hn L rs, phaseW_isQ hn L rs, ?_, phaseW_fix hn L rs hX hY, ?_⟩
  · rw [phaseW_length]; exact h3
  · intro i hi j hj k
    rw [phaseW_on hn L rs hX hY i j (hR i hi) (hC j hj), h2 i hi j hj]
    by_cases hm : M i j <;> simp [hm]

/-- A whole sequence of letters, with an arbitrary sublist chosen on each orbit. -/
theorem parallel_seq (hn : 2 ≤ n) (hR : ∀ i ∈ R, IsRow i) (hC : ∀ j ∈ C, IsCol j)
    (s : ℕ) (hs : 0 < s) : ∀ (Seq : List Letter) (S : Fin n → Fin n → List Letter),
    (∀ i ∈ R, ∀ j ∈ C, (S i j).Sublist Seq) →
    ∃ W : Word n, (∀ m ∈ W, IsQ m) ∧ W.length ≤ Seq.length * phaseCost R.card C.card s ∧
      FixesSkel hn W ∧ ∀ i ∈ R, ∀ j ∈ C, ∀ k,
        Word.eval W (e (rep i j) k) = e (rep i j) (prodL (S i j) k) := by
  intro Seq
  induction Seq with
  | nil =>
    intro S hS
    refine ⟨[], by simp, by simp, FixesSkel.nil hn, ?_⟩
    intro i hi j hj k
    have : S i j = [] := List.sublist_nil.1 (hS i hi j hj)
    simp [this, prodL]
  | cons L rest ih =>
    intro S hS
    let M : Fin n → Fin n → Prop := fun i j => ¬ (S i j).Sublist rest
    let S' : Fin n → Fin n → List Letter := fun i j =>
      if (S i j).Sublist rest then S i j else (S i j).tail
    have hsplit : ∀ i ∈ R, ∀ j ∈ C, (S' i j).Sublist rest ∧
        S i j = (if M i j then [L] else []) ++ S' i j := by
      intro i hi j hj
      by_cases h : (S i j).Sublist rest
      · simp [S', M, h]
      · have h' := hS i hi j hj
        rw [List.sublist_cons_iff] at h'
        obtain ⟨r, hr, hrs⟩ := h'.resolve_left h
        simp only [S', M, h, if_false, not_false_eq_true, if_true]
        rw [hr]
        simpa using hrs
    obtain ⟨W, a1, a2, a3, a4⟩ := ih S' (fun i hi j hj => (hsplit i hi j hj).1)
    obtain ⟨w, b1, b2, b3, b4⟩ := phase_exists hn L hR hC s hs M
    refine ⟨w ++ W, ?_, ?_, b3.append a3, ?_⟩
    · intro m hm
      rcases List.mem_append.1 hm with h | h
      · exact b1 m h
      · exact a1 m h
    · simp only [List.length_append, List.length_cons]
      nlinarith [b2, a2]
    · intro i hi j hj k
      simp only [Word.eval_append, Perm.mul_apply]
      rw [a4 i hi j hj k, b4 i hi j hj]
      congr 1
      have h := (hsplit i hi j hj).2
      by_cases hm : M i j
      · rw [if_pos hm] at h ⊢
        rw [h]
        simp [prodL]
      · rw [if_neg hm] at h ⊢
        rw [h]
        rfl

end RubiksGN
