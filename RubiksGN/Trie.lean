import RubiksGN.Program
import RubiksGN.TrieCost

/-!
# Trie slots: consecutive slots of a pass cancel

A pass is a product of slots `G(p) · T(p) · G(p)⁻¹` with `G(p) = g₁(p₁) ⋯ g_s(p_s)`. Played in lexicographic order,
`G(p)⁻¹ G(p')` cancels freely on the common prefix of `p` and `p'`. So only the edges of the trie of the patterns are
played, twice each, instead of all `2 s` templates of all slots.

`trieWord` is the word of the trie, by recursion on the rows, and `trieOrder` the order of its slots: a permutation of
the given list of patterns. `trieW` is the pass written in this way, with the same action as `passW` on all orbits
(`trieW_Rv`), and with `|Y|` column moves and the moves of the edges only (`trieW_length`). If all values lie in a list `l`
of `m` values, of total length `w`, then the edges cost at most `2 w (1 + m + ⋯ + m^(s-1))` (`trieCost_le`).
-/

open Equiv

namespace RubiksGN

variable {n : ℕ} {ρ β : Type*}

/-! ### The trie of a list of patterns -/

section Generic

variable [DecidableEq β]

/-- The word of the trie: go down an edge, play the subtree, come back. The slots act at the leaves. -/
def trieWord (t : ρ → β → Word n) (A : (ρ → β) → Word n) : List ρ → List (ρ → β) → Word n
  | [], P => P.flatMap A
  | r :: rs, P => (P.map fun p => p r).dedup.flatMap fun a =>
      t r a ++ trieWord t A rs (P.filter fun p => p r = a) ++ Word.inv (t r a)

/-- The order of the slots in the trie. -/
def trieOrder : List ρ → List (ρ → β) → List (ρ → β)
  | [], P => P
  | r :: rs, P => (P.map fun p => p r).dedup.flatMap fun a =>
      trieOrder rs (P.filter fun p => p r = a)

/-- The cost of the edges of the trie, with `ω a` the length of an edge of value `a`, played twice. -/
def trieCost (ω : β → ℕ) : List ρ → List (ρ → β) → ℕ
  | [], _ => 0
  | r :: rs, P => ((P.map fun p => p r).dedup.map fun a =>
      2 * ω a + trieCost ω rs (P.filter fun p => p r = a)).sum

/-- The conjugator of a pattern. -/
def trieG (t : ρ → β → Word n) (rs : List ρ) (p : ρ → β) : Word n := rs.flatMap fun r => t r (p r)

theorem trieOrder_perm : ∀ (rs : List ρ) (P : List (ρ → β)), P.Nodup → (trieOrder rs P).Perm P := by
  intro rs
  induction rs with
  | nil => intro P _; exact List.Perm.refl _
  | cons r rs ih =>
    intro P hP
    simp only [trieOrder]
    refine List.Perm.trans ?_ (perm_flatMap_filter (P.map fun p => p r).dedup (List.nodup_dedup _) P hP
      (fun p => p r) (fun x hx => List.mem_dedup.2 (List.mem_map_of_mem hx)))
    exact List.Perm.flatMap_left _ fun a _ => ih _ (hP.filter _)

theorem mem_trieOrder (rs : List ρ) (P : List (ρ → β)) (hP : P.Nodup) {p : ρ → β}
    (hp : p ∈ trieOrder rs P) : p ∈ P :=
  (trieOrder_perm rs P hP).subset hp

theorem prod_map_flatMap {ι κ G : Type*} [Monoid G] (f : ι → List κ) (g : κ → G) (l : List ι) :
    ((l.flatMap f).map g).prod = (l.map fun x => ((f x).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

theorem sum_map_flatMap {ι κ : Type*} (f : ι → List κ) (g : κ → ℕ) (l : List ι) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

theorem conj_list_prod {ι G : Type*} [Group G] (g : G) (f : ι → G) (l : List ι) :
    g * (l.map f).prod * g⁻¹ = (l.map fun x => g * f x * g⁻¹).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, ← ih]
    group

/-- **The action of the trie.** It is the product of the slots, in the order of the trie. -/
theorem Rv_trieWord (v : Sticker n) (t : ρ → β → Word n) (ht : ∀ r a, ∀ m ∈ t r a, IsQ m)
    (A : (ρ → β) → Word n) : ∀ (rs : List ρ) (P : List (ρ → β)), P.Nodup →
    Rv v (trieWord t A rs P) = ((trieOrder rs P).map fun p =>
      Rv v (trieG t rs p) * Rv v (A p) * (Rv v (trieG t rs p))⁻¹).prod := by
  intro rs
  induction rs with
  | nil =>
    intro P _
    simp [trieWord, trieOrder, trieG, Rv_flatMap]
  | cons r rs ih =>
    intro P hP
    simp only [trieWord, trieOrder, Rv_flatMap, Rv_append, Rv_inv v _ (ht _ _), prod_map_flatMap]
    congr 1
    apply List.map_congr_left
    intro a _
    rw [ih _ (hP.filter _), conj_list_prod]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hpa : p r = a := by
      have := mem_trieOrder rs _ (hP.filter _) hp
      simpa using (List.mem_filter.1 this).2
    have e : trieG t (r :: rs) p = t r a ++ trieG t rs p := by
      simp [trieG, hpa]
    rw [e, Rv_append, mul_inv_rev]
    group

/-- All the moves are quarter turns. -/
theorem trieWord_isQ (t : ρ → β → Word n) (ht : ∀ r a, ∀ m ∈ t r a, IsQ m)
    (A : (ρ → β) → Word n) (hA : ∀ p, ∀ m ∈ A p, IsQ m) :
    ∀ (rs : List ρ) (P : List (ρ → β)), ∀ m ∈ trieWord t A rs P, IsQ m := by
  intro rs
  induction rs with
  | nil =>
    intro P m hm
    obtain ⟨p, _, h⟩ := List.mem_flatMap.1 hm
    exact hA p m h
  | cons r rs ih =>
    intro P m hm
    obtain ⟨a, _, h⟩ := List.mem_flatMap.1 hm
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact ht r a m h
      · exact ih _ m h
    · exact Word.inv_isQ _ (ht r a) m h

/-- The length of the trie: the leaves and the edges. -/
theorem trieWord_length (t : ρ → β → Word n) (ω : β → ℕ) (hω : ∀ r a, (t r a).length = ω a)
    (A : (ρ → β) → Word n) : ∀ (rs : List ρ) (P : List (ρ → β)),
    (trieWord t A rs P).length = ((trieOrder rs P).map fun p => (A p).length).sum + trieCost ω rs P := by
  intro rs
  induction rs with
  | nil =>
    intro P
    simp [trieWord, trieOrder, trieCost, List.length_flatMap]
  | cons r rs ih =>
    intro P
    simp only [trieWord, trieOrder, trieCost, List.length_flatMap, sum_map_flatMap]
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro a _
    simp only [List.length_append, Word.inv_length, hω, ih]
    ring

/-- **The cost of the edges.** All values lie in a list of `m` values, of total length `w`. -/
theorem trieCost_le (ω : β → ℕ) (l : List β) : ∀ (rs : List ρ) (P : List (ρ → β)),
    (∀ p ∈ P, ∀ r ∈ rs, p r ∈ l) →
    trieCost ω rs P ≤ 2 * (l.map ω).sum * geomS l.length rs.length := by
  intro rs
  induction rs with
  | nil => intro P _; simp [trieCost, geomS]
  | cons r rs ih =>
    intro P hP
    set vals := (P.map fun p => p r).dedup with hvals
    have hsub : vals ⊆ l := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 ha)
      exact hP p hp r List.mem_cons_self
    have hsp : vals.Subperm l := (List.nodup_dedup _).subperm hsub
    have hlen : vals.length ≤ l.length := hsp.length_le
    have hw : (vals.map ω).sum ≤ (l.map ω).sum := by
      obtain ⟨l', hl', hs'⟩ := hsp
      rw [← (hl'.map ω).sum_eq]
      exact (hs'.map ω).sum_le_sum (fun _ _ => Nat.zero_le _)
    set C := 2 * (l.map ω).sum * geomS l.length rs.length with hC
    have step : ∀ V : List β, (∀ a ∈ V, trieCost ω rs (P.filter fun p => p r = a) ≤ C) →
        (V.map fun a => 2 * ω a + trieCost ω rs (P.filter fun p => p r = a)).sum ≤
          2 * (V.map ω).sum + V.length * C := by
      intro V
      induction V with
      | nil => simp
      | cons a t iht =>
        intro h
        have h1 := h a List.mem_cons_self
        have h2 := iht (fun b hb => h b (List.mem_cons_of_mem _ hb))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
    have h1 := step vals (fun a _ => ih _ (fun p hp r' hr' =>
      hP p (List.mem_filter.1 hp).1 r' (List.mem_cons_of_mem _ hr')))
    simp only [trieCost, ← hvals]
    refine h1.trans ?_
    simp only [List.length_cons, geomS]
    have h3 : vals.length * C ≤ l.length * C := Nat.mul_le_mul_right _ hlen
    have e : 2 * (l.map ω).sum * (1 + l.length * geomS l.length rs.length) =
        2 * (l.map ω).sum + l.length * C := by
      rw [hC]; ring
    rw [e]
    omega

end Generic

/-! ### A pass, written as a trie -/

section Pass

variable {α : Type*} [DecidableEq α]

/-- **A pass as a trie.** -/
noncomputable def trieW (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl) (pat : Fin n → Fin n → α)
    (d : Bool) : Word n :=
  trieWord (fun (i : X) a => tmplW hn i.1 (τ a))
    (fun p => (colsOf X Y pat p).map fun j => ((.x, j, dirTurn d) : Move n))
    X.attach.toList (patsOf X Y pat).toList

/-- The edges of a pass. -/
noncomputable def passEdges (X Y : Finset (Fin n)) (τ : α → Tmpl) (pat : Fin n → Fin n → α) : ℕ :=
  trieCost (fun a => tmplLen (τ a)) X.attach.toList (patsOf X Y pat).toList

theorem trieW_isQ (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl) (pat : Fin n → Fin n → α) (d : Bool) :
    ∀ m ∈ trieW hn X Y τ pat d, IsQ m := by
  apply trieWord_isQ
  · intro r a
    exact tmplW_isQ hn r.1 _
  · intro p m hm
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hm
    cases d <;> simp [IsQ, dirTurn]

/-- **The length of a pass as a trie**: `|Y|` plus the edges. -/
theorem trieW_length (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl) (pat : Fin n → Fin n → α) (d : Bool) :
    (trieW hn X Y τ pat d).length = Y.card + passEdges X Y τ pat := by
  rw [trieW, trieWord_length (fun (i : X) a => tmplW hn i.1 (τ a)) (fun a => tmplLen (τ a))
    (fun r a => tmplW_length hn r.1 _), passEdges]
  congr 1
  have h1 := (trieOrder_perm X.attach.toList (patsOf X Y pat).toList (Finset.nodup_toList _))
  have h2 : ((trieOrder X.attach.toList (patsOf X Y pat).toList).map fun p =>
      (((colsOf X Y pat p).map fun j => ((.x, j, dirTurn d) : Move n))).length).sum =
      ((patsOf X Y pat).toList.map fun p => (colsOf X Y pat p).length).sum := by
    simp only [List.length_map]
    exact (h1.map _).sum_eq
  rw [h2, ← List.length_flatMap, (perm_cols X Y pat).length_eq, Finset.length_toList]

/-- The action of a pass as a trie: the slots, in the order of the trie. -/
theorem Rv_trieW (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) :
    Rv v (trieW hn X Y τ pat d) = ((trieOrder X.attach.toList (patsOf X Y pat).toList).map fun p =>
      Rv v (gW hn X τ p) * ((colsOf X Y pat p).map (colT v d)).prod * (Rv v (gW hn X τ p))⁻¹).prod := by
  rw [trieW, Rv_trieWord v (fun (i : X) a => tmplW hn i.1 (τ a)) (fun r _ => tmplW_isQ hn r.1 _) _ _ _
    (Finset.nodup_toList _)]
  congr 1
  apply List.map_congr_left
  intro p _
  have h : Rv v ((colsOf X Y pat p).map fun j => ((.x, j, dirTurn d) : Move n)) =
      ((colsOf X Y pat p).map (colT v d)).prod := by
    simp only [Rv, List.map_map]
    rfl
  rw [h]
  rfl

/-- No column of the pass touches the orbit. -/
theorem trie_trivial (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) (h : ∀ j ∈ Y, colT v d j = 1) :
    Rv v (trieW hn X Y τ pat d) = 1 := by
  rw [Rv_trieW]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  have : ((colsOf X Y pat p).map (colT v d)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact h j (Finset.mem_toList.1 (List.mem_filter.1 hj).1)
  rw [this]
  simp

/-- Only the slot of one column can act. -/
theorem slot_of_single (v : Sticker n) (hn : 2 ≤ n) (X Y : Finset (Fin n)) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {j₀ : Fin n} (h : ∀ j ∈ Y, j ≠ j₀ → colT v d j = 1)
    {p : X → α} (hp : p ≠ patOf X pat j₀) :
    Rv v (gW hn X τ p) * ((colsOf X Y pat p).map (colT v d)).prod * (Rv v (gW hn X τ p))⁻¹ = 1 := by
  have : ((colsOf X Y pat p).map (colT v d)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hjY, hjp⟩ := List.mem_filter.1 hj
    apply h j (Finset.mem_toList.1 hjY)
    rintro rfl
    exact hp (of_decide_eq_true hjp).symm
  rw [this]
  simp

/-- **The action does not depend on the order of the slots.** A pass as a trie acts as `passW` on all orbits. -/
theorem trieW_Rv (hn : 2 ≤ n) {X Y : Finset (Fin n)} (c : PairCtx X Y) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) {i j : Fin n} (hi : IsRow i) (hj : IsCol j) :
    Rv (rep i j) (trieW hn X Y τ pat d) = Rv (rep i j) (passW hn X Y τ pat d) := by
  rw [Rv_trieW, Rv_passW]
  set v := rep i j with hv
  set f : (X → α) → Perm (Fin 24) := fun p =>
    Rv v (gW hn X τ p) * ((colsOf X Y pat p).map (colT v d)).prod * (Rv v (gW hn X τ p))⁻¹ with hf
  have hperm := trieOrder_perm X.attach.toList (patsOf X Y pat).toList (Finset.nodup_toList _)
  have hnd : (trieOrder X.attach.toList (patsOf X Y pat).toList).Nodup :=
    hperm.nodup_iff.2 (Finset.nodup_toList _)
  apply List.Perm.prod_eq' (hperm.map f)
  rw [List.pairwise_map]
  -- a single column touches the orbit
  have single : ∀ j₀ : Fin n, (∀ j' ∈ Y, j' ≠ j₀ → colT v d j' = 1) →
      (trieOrder X.attach.toList (patsOf X Y pat).toList).Pairwise fun a b => Commute (f a) (f b) := by
    intro j₀ h
    refine List.Pairwise.imp ?_ hnd
    intro a b hab
    by_cases ha : a = patOf X pat j₀
    · have hb : b ≠ patOf X pat j₀ := fun hb => hab (ha.trans hb.symm)
      have : f b = 1 := slot_of_single v hn X Y τ pat d h hb
      rw [this]
      exact Commute.one_right _
    · have : f a = 1 := slot_of_single v hn X Y τ pat d h ha
      rw [this]
      exact Commute.one_left _
  by_cases hiX : i ∈ X
  · refine single j fun j' hj' hne => ?_
    apply rvL_col_clear
    refine clear_col c hi hj hj' hne ?_
    rintro rfl
    exact c.hXY i hiX _ hj' (by rw [layerZ_rev])
  by_cases hrj : Fin.rev j ∈ X
  · refine single (Fin.rev i) fun j' hj' hne => ?_
    apply rvL_col_clear
    refine clear_col c hi hj hj' ?_ hne
    rintro rfl
    exact c.hXY _ hrj _ hj' (by rw [layerZ_rev]; ring)
  -- no conjugator acts on the orbit
  have hG : ∀ p, Rv v (gW hn X τ p) = 1 := fun p =>
    Rv_gW_clear hn X τ p i j fun i' hi' => clear_row (c.hX i' hi') hi hj
      (fun he => hiX (he ▸ hi')) (fun he => hrj (he ▸ hi'))
  refine List.Pairwise.imp ?_ hnd
  intro a b _
  simp only [hf, hG, one_mul, inv_one, mul_one]
  apply Commute.list_prod_left
  intro x hx
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨j₁, _, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j₂, _, rfl⟩ := List.mem_map.1 hy
  exact colT_commute v d d _ _

/-- A pass as a trie fixes the skeleton: its columns miss these orbits. -/
theorem trieW_fixesSkel (hn : 2 ≤ n) {X Y : Finset (Fin n)}
    (hY : ∀ j ∈ Y, 0 < layerZ n j ∧ layerZ n j < (n : ℤ) - 1) (τ : α → Tmpl)
    (pat : Fin n → Fin n → α) (d : Bool) : FixesSkel hn (trieW hn X Y τ pat d) := by
  have key : ∀ i j : Fin n, (∀ j' ∈ Y, Clear n (layerZ n i) (layerZ n j) (layerZ n j')) → ∀ k,
      Word.eval (trieW hn X Y τ pat d) (e (rep i j) k) = e (rep i j) k := by
    intro i j h k
    have this : Rv (rep i j) (trieW hn X Y τ pat d) = 1 :=
      trie_trivial _ hn X Y τ pat d (fun j' hj' => rvL_col_clear i j j' (h j' hj') d)
    rw [eval_of_Rv _ _ (trieW_isQ hn X Y τ pat d) this]
    rfl
  constructor
  · intro j hj k
    apply key
    intro j' hj'
    have a := hY j' hj'
    have h0 : layerZ n (⟨0, by omega⟩ : Fin n) = -((n : ℤ) - 1) := by simp [layerZ]
    have h1 : layerZ n j = (n : ℤ) - 1 ∨ layerZ n j = 0 := by
      rcases hj with rfl | hj
      · exact Or.inl (layerZ_topI hn)
      · exact Or.inr hj
    rw [h0]
    simp only [Clear]
    omega
  · intro m hm k
    apply key
    intro j' hj'
    have a := hY j' hj'
    rw [hm]
    simp only [Clear]
    omega

end Pass

end RubiksGN
