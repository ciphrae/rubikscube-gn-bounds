import RubiksGN.Orbit

/-!
# Verified stabilizer chains

A `Level` is a transversal, a chain is a list of levels, and `InP ls g` says `g` is a product of one
entry per level. The checker `chainCheck` proves that this set is a group containing all squares and
commutators of the generating moves; hence it contains the value of any word in which every layer is
turned an even number of times.
-/

open Equiv

namespace RubiksGN

/-- Symbolic moves: axis, layer (`0` the negative outer layer, `1` the middle, `2` the positive outer
layer), direction. -/
abbrev Sym := Axis × Fin 3 × Bool

/-- All symbolic moves. -/
def allSyms : List Sym :=
  [Axis.x, Axis.y, Axis.z].flatMap fun a =>
    [(0 : Fin 3), 1, 2].flatMap fun l => [true, false].map fun d => (a, l, d)

/-- Inverse of a symbolic word. -/
def Sym.flip (s : Sym) : Sym := (s.1, s.2.1, !s.2.2)

/-- A permutation as a table: base-32 digits packed in one natural number. -/
abbrev Tb := ℕ

/-- Evaluate a natural number before continuing: the kernel reduces lazily, and without this an
unevaluated table would be recomputed at each use. -/
def force {α : Type} (g : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn g (k 0) (fun m => k (m + 1))

theorem force_eq {α : Type} (g : ℕ) (k : ℕ → α) : force g k = k g := by
  cases g <;> rfl

/-- Read a digit. -/
def getT (t : Tb) (i : ℕ) : ℕ := (t >>> (5 * i)) % 32

/-- Pack a list of digits. -/
def packT : List ℕ → Tb
  | [] => 0
  | v :: l => v % 32 + 32 * packT l

theorem getT_pack (l : List ℕ) (i : ℕ) : getT (packT l) i = l.getD i 0 % 32 := by
  simp only [getT, Nat.shiftRight_eq_div_pow]
  induction l generalizing i with
  | nil => simp [packT]
  | cons v l ih =>
    cases i with
    | zero => simp [packT]
    | succ i =>
      have h := ih i
      simp only [List.getD_cons_succ]
      rw [← h, packT]
      have : 2 ^ (5 * (i + 1)) = 32 * 2 ^ (5 * i) := by
        rw [show 5 * (i + 1) = 5 + 5 * i by ring, pow_add]; norm_num
      rw [this, ← Nat.div_div_eq_div_mul]
      congr 2
      omega

/-- The list `[0, …, N-1]`, kept separate so that it is only computed once per table. -/
def rangeT (N : ℕ) : List ℕ := List.range N

/-- Composition of tables: `(p * q) i = p (q i)`. -/
def compT (N : ℕ) (p q : Tb) : Tb := packT ((rangeT N).map fun i => getT p (getT q i))

/-- An entry of a transversal. -/
structure Entry where
  w : List Sym
  t : Tb
  ti : Tb

/-- A level: its base point and its transversal. -/
structure Level where
  b : ℕ
  es : List Entry

section Generic

variable {N : ℕ}

/-- `t` is the table of `g`. -/
def Rep (g : Perm (Fin N)) (t : Tb) : Prop := ∀ i : Fin N, (g i).val = getT t i

theorem Rep.mul {g h : Perm (Fin N)} {t u : Tb} (hg : Rep g t) (hh : Rep h u) :
    Rep (g * h) (compT N t u) := by
  intro i
  have hlt : i.val < (rangeT N).length := by simp [rangeT]
  simp only [compT, getT_pack]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp only [List.getElem_map, rangeT, List.getElem_range, Perm.mul_apply]
  have h1 : (h i).val = getT u i := hh i
  have h2 : getT t (getT u i) = (g (h i)).val := by rw [← h1]; exact (hg (h i)).symm
  rw [h2]
  have : getT t (getT u i) < 32 := Nat.mod_lt _ (by norm_num)
  rw [h2] at this
  exact (Nat.mod_eq_of_lt this).symm

/-- The identity table. -/
def idT (N : ℕ) : Tb := packT (rangeT N)

theorem rep_one (hN : N ≤ 32) : Rep (1 : Perm (Fin N)) (idT N) := by
  intro i
  have hlt : i.val < (rangeT N).length := by simp [rangeT]
  simp only [idT, getT_pack, Perm.one_apply]
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [rangeT, List.getElem_range]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem Rep.ext {g h : Perm (Fin N)} {t : Tb} (hg : Rep g t) (hh : Rep h t) : g = h := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [hg, hh]

variable (sp : Sym → Perm (Fin N)) (sT : Sym → Tb)

/-- The value of a symbolic word. -/
def evalS (w : List Sym) : Perm (Fin N) := (w.map sp).prod

/-- The table of a symbolic word. -/
def tbOf (N : ℕ) (sT : Sym → Tb) : List Sym → Tb
  | [] => idT N
  | s :: w => force (tbOf N sT w) fun r => compT N (sT s) r

/-- The inverse symbolic word. -/
def flipW (w : List Sym) : List Sym := (w.map Sym.flip).reverse

theorem flipW_length (w : List Sym) : (flipW w).length = w.length := by simp [flipW]

variable {sp sT}

theorem tbOf_rep (hN : N ≤ 32) (hs : ∀ s, Rep (sp s) (sT s)) (w : List Sym) :
    Rep (evalS sp w) (tbOf N sT w) := by
  induction w with
  | nil => simpa [evalS, tbOf] using rep_one hN
  | cons s t ih => simpa [evalS, tbOf, force_eq] using (hs s).mul ih

variable (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹)
include hflip

theorem evalS_flipW (w : List Sym) : evalS sp (flipW w) = (evalS sp w)⁻¹ := by
  induction w with
  | nil => simp [evalS, flipW]
  | cons s t ih =>
    simp only [evalS, flipW, List.map_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_inv_rev] at ih ⊢
    rw [ih, hflip]

omit hflip

variable (sp) in
/-- A product of one entry per level. -/
def InP : List Level → Perm (Fin N) → Prop
  | [], g => g = 1
  | l :: ls, g => ∃ e ∈ l.es, ∃ h, InP ls h ∧ g = evalS sp e.w * h

/-- Decide membership by sifting. -/
def inP (N : ℕ) : List Level → Tb → Bool
  | [], g => g == idT N
  | l :: ls, g =>
    force (getT g l.b) fun x =>
      match l.es.find? (fun e => getT e.t l.b == x) with
      | none => false
      | some e => force (compT N e.ti g) fun g' => inP N ls g'

/-- Entries carry correct tables. -/
def entryOK (N : ℕ) (sT : Sym → Tb) (e : Entry) : Bool :=
  e.t == tbOf N sT e.w && e.ti == tbOf N sT (flipW e.w)

/-- All entries of a chain. -/
def gensOf (ls : List Level) : List Entry := ls.flatMap fun l => l.es

theorem inP_sound (hN : N ≤ 32) (hs : ∀ s, Rep (sp s) (sT s)) (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹) :
    ∀ (ls : List Level), (∀ e ∈ gensOf ls, entryOK N sT e = true) →
      ∀ (g : Perm (Fin N)) (t : Tb), Rep g t → inP N ls t = true → InP sp ls g := by
  intro ls
  induction ls with
  | nil =>
    intro _ g t hg h
    simp only [inP, beq_iff_eq] at h
    subst h
    exact hg.ext (rep_one hN)
  | cons l ls ih =>
    intro hok g t hg h
    simp only [inP, force_eq] at h
    cases hf : l.es.find? (fun e => getT e.t l.b == getT t l.b) with
    | none => rw [hf] at h; simp at h
    | some e =>
      rw [hf] at h
      have hem : e ∈ l.es := List.mem_of_find?_eq_some hf
      have hee := hok e (by simp only [gensOf, List.flatMap_cons]; exact List.mem_append_left _ hem)
      simp only [entryOK, Bool.and_eq_true, beq_iff_eq] at hee
      have hti : Rep (evalS sp e.w)⁻¹ e.ti := by
        rw [hee.2, ← evalS_flipW hflip]
        exact tbOf_rep hN hs _
      have hg' := hti.mul hg
      refine ⟨e, hem, _, ih (fun x hx => hok x ?_) _ _ hg' h, by simp⟩
      simp only [gensOf, List.flatMap_cons]
      exact List.mem_append_right _ hx

theorem mem_mul_of_gens (X : Set (Perm (Fin N))) :
    ∀ (ls : List Level), (∀ e ∈ gensOf ls, ∀ g ∈ X, evalS sp e.w * g ∈ X) →
      ∀ u, InP sp ls u → ∀ h ∈ X, u * h ∈ X := by
  intro ls
  induction ls with
  | nil =>
    intro _ u hu h hh
    simp only [InP] at hu
    subst hu
    simpa using hh
  | cons l ls ih =>
    intro hX u hu h hh
    obtain ⟨e, he, v, hv, rfl⟩ := hu
    have hv' := ih (fun x hx g hg => hX x (by
      simp only [gensOf, List.flatMap_cons]; exact List.mem_append_right _ hx) g hg) v hv h hh
    rw [_root_.mul_assoc]
    exact hX e (by simp only [gensOf, List.flatMap_cons]; exact List.mem_append_left _ he) _ hv'

/-- The closure test: left multiplication by a strong generator preserves each partial product. -/
def closedOK (N : ℕ) : List Level → Bool
  | [] => true
  | l :: ls => closedOK N ls &&
      l.es.any (fun e => e.w.isEmpty) &&
      (gensOf (l :: ls)).all fun s => l.es.all fun e =>
        force (compT N s.t e.t) fun g => inP N (l :: ls) g

theorem entry_rep (hN : N ≤ 32) (hs : ∀ s, Rep (sp s) (sT s)) {e : Entry} (h : entryOK N sT e = true) :
    Rep (evalS sp e.w) e.t := by
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1]
  exact tbOf_rep hN hs _

theorem closed_sound (hN : N ≤ 32) (hs : ∀ s, Rep (sp s) (sT s)) (hflip : ∀ s, sp (Sym.flip s) = (sp s)⁻¹) :
    ∀ (ls : List Level), (∀ e ∈ gensOf ls, entryOK N sT e = true) → closedOK N ls = true →
      InP sp ls 1 ∧ ∀ s ∈ gensOf ls, ∀ g, InP sp ls g → InP sp ls (evalS sp s.w * g) := by
  intro ls
  induction ls with
  | nil => intro _ _; simp [InP, gensOf]
  | cons l ls ih =>
    intro hok hc
    simp only [closedOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, force_eq] at hc
    obtain ⟨⟨hc1, ⟨e0, he0, hemp⟩⟩, hc3⟩ := hc
    have hsub : ∀ x ∈ gensOf ls, x ∈ gensOf (l :: ls) := fun x hx => by
      simp only [gensOf, List.flatMap_cons]; exact List.mem_append_right _ hx
    obtain ⟨h1, h2⟩ := ih (fun x hx => hok x (hsub x hx)) hc1
    constructor
    · refine ⟨e0, he0, 1, h1, ?_⟩
      have : e0.w = [] := List.isEmpty_iff.1 hemp
      simp [this, evalS]
    · rintro s hs' g ⟨e, he, h, hh, rfl⟩
      have hes := entry_rep hN hs (hok s hs')
      have hee := entry_rep hN hs (hok e (by
        simp only [gensOf, List.flatMap_cons]; exact List.mem_append_left _ he))
      have hin := inP_sound hN hs hflip (l :: ls) hok _ _ (hes.mul hee) (hc3 s hs' e he)
      obtain ⟨e', he', u, hu, heq⟩ := hin
      refine ⟨e', he', u * h, ?_, ?_⟩
      · exact mem_mul_of_gens {g | InP sp ls g} ls (fun x hx g hg => h2 x hx g hg) u hu h hh
      · rw [← _root_.mul_assoc, heq, _root_.mul_assoc]

/-- The subgroup generated by the strong generators. -/
def groupOf (sp : Sym → Perm (Fin N)) (ls : List Level) : Subgroup (Perm (Fin N)) :=
  Subgroup.closure {g | ∃ e ∈ gensOf ls, g = evalS sp e.w}

theorem InP_mem : ∀ (ls ls' : List Level), (∀ x ∈ gensOf ls, x ∈ gensOf ls') →
    ∀ g, InP sp ls g → g ∈ groupOf sp ls' := by
  intro ls
  induction ls with
  | nil =>
    intro ls' _ g hg
    simp only [InP] at hg
    subst hg
    exact one_mem _
  | cons l ls ih =>
    rintro ls' hsub g ⟨e, he, h, hh, rfl⟩
    refine mul_mem (Subgroup.subset_closure ⟨e, hsub e ?_, rfl⟩) (ih ls' (fun x hx => hsub x ?_) h hh)
    · simp only [gensOf, List.flatMap_cons]; exact List.mem_append_left _ he
    · simp only [gensOf, List.flatMap_cons]; exact List.mem_append_right _ hx

theorem mem_InP {ls₀ : List Level} (h1 : InP sp ls₀ 1)
    (h2 : ∀ s ∈ gensOf ls₀, ∀ g, InP sp ls₀ g → InP sp ls₀ (evalS sp s.w * g))
    (g : Perm (Fin N)) (hg : g ∈ groupOf sp ls₀) : InP sp ls₀ g := by
  have key : ∀ x ∈ groupOf sp ls₀, ∀ h, InP sp ls₀ h → InP sp ls₀ (x * h) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨e, he, rfl⟩ := hy
      exact h2 e he
    | one => simp
    | mul y z _ _ iy iz =>
      intro h hh
      rw [_root_.mul_assoc]
      exact iy _ (iz _ hh)
    | inv y _ iy =>
      intro h hh
      have hpow : ∀ k : ℕ, InP sp ls₀ (y ^ k * h) := by
        intro k
        induction k with
        | zero => simpa using hh
        | succ k ik =>
          rw [pow_succ', _root_.mul_assoc]
          exact iy _ ik
      have hinv : y⁻¹ = y ^ (orderOf y - 1) := by
        have hp := orderOf_pos y
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel hp, pow_orderOf_eq_one]
      rw [hinv]
      exact hpow _
  simpa using key g hg 1 h1

end Generic

/-! ### Words in which every layer turns an even number of times -/

section Even

variable {Γ ℓ κ : Type*} [Group Γ] [BEq κ] [LawfulBEq κ] (f : ℓ → Γ) (key : ℓ → κ) (K : Subgroup Γ)

/-- Abelianisation modulo `K`: a word with even key counts evaluates into `K`. -/
theorem even_word_mem (hsame : ∀ l l', key l = key l' → f l * f l' ∈ K)
    (hcomm : ∀ l l', f l * f l' * (f l)⁻¹ * (f l')⁻¹ ∈ K)
    (hconj : ∀ l, ∀ k ∈ K, f l * k * (f l)⁻¹ ∈ K)
    (hinv : ∀ l, ∃ l', f l' = (f l)⁻¹ ∧ key l' = key l) :
    ∀ (m : ℕ) (w : List ℓ), w.length = m → (∀ c : κ, Even ((w.map key).count c)) →
      (w.map f).prod ∈ K := by
  have hA : ∀ (x : ℓ) (u : List ℓ),
      (u.map f).prod * f x * ((u.map f).prod)⁻¹ * (f x)⁻¹ ∈ K := by
    intro x u
    induction u with
    | nil => simp
    | cons a t ih =>
      have h1 := hconj a _ ih
      have h2 := hcomm a x
      have := mul_mem h1 h2
      simp only [List.map_cons, List.prod_cons, mul_inv_rev]
      convert this using 1
      group
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw he
    cases w with
    | nil => simp
    | cons l rest =>
      have hc := he (key l)
      simp only [List.map_cons, List.count_cons_self] at hc
      have hodd : 0 < (rest.map key).count (key l) := by
        rcases Nat.eq_zero_or_pos ((rest.map key).count (key l)) with h0 | h0
        · rw [h0] at hc; simp at hc
        · exact h0
      obtain ⟨y, hy, hyk⟩ := List.mem_map.1 (List.count_pos_iff.1 hodd)
      obtain ⟨u, v, rfl⟩ := List.append_of_mem hy
      obtain ⟨x, hxf, _⟩ := hinv y
      have hlen : (u ++ v).length < m := by
        simp only [List.length_cons, List.length_append] at hw ⊢
        omega
      have heven : ∀ c : κ, Even (((u ++ v).map key).count c) := by
        intro c
        have := he c
        simp only [List.map_cons, List.map_append, List.count_append, List.count_cons] at this ⊢
        by_cases hcl : key l = c
        · have hcy : key y = c := hyk.trans hcl
          simp only [hcl, hcy, if_true, beq_self_eq_true] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨r - 1, by omega⟩
        · have hcy : key y ≠ c := fun h => hcl (hyk.symm.trans h)
          simpa [hcl, hcy] using this
      have hrec := ih _ hlen (u ++ v) rfl heven
      have h1 : f l * f y ∈ K := hsame l y hyk.symm
      have h2 := K.inv_mem (hA x u)
      have h3 := mul_mem (mul_mem h1 h2) hrec
      simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append] at hrec ⊢
      convert h3 using 1
      simp only [List.map_append, List.prod_append, hxf]
      group

end Even

end RubiksGN
