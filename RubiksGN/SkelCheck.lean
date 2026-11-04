import RubiksGN.SkelData

/-!
# Kernel verification of the corner, edge and centre chains
-/

namespace RubiksGN

/-- Same axis and same layer. -/
def Sym.sameKey (s s' : Sym) : Bool := s.1 == s'.1 && s.2.1 == s'.2.1

/-- Evenness of a symbolic word: every layer of every axis turns an even number of times. -/
def evenS (w : List Sym) : Bool :=
  allSyms.all fun s => (w.countP fun s' => Sym.sameKey s s') % 2 == 0

/-- The table of a symbol. -/
def tableOf (tab : List Tb) (s : Sym) : Tb := tab.getD (symIdx s) 0

/-- The full check of a chain: tables, group closure, squares, commutators, normality. -/
def chainCheck (N : ℕ) (tab : List Tb) (ls : List Level) : Bool :=
  let sT := tableOf tab
  (gensOf ls).all (entryOK N sT) && closedOK N ls &&
  allSyms.all (fun s => allSyms.all fun s' =>
    (!Sym.sameKey s s' || inP N ls (compT N (sT s) (sT s'))) &&
    inP N ls (compT N (compT N (compT N (sT s) (sT s')) (sT s.flip)) (sT s'.flip))) &&
  allSyms.all fun s => (gensOf ls).all fun e =>
    inP N ls (compT N (compT N (sT s) e.t) (sT s.flip))

set_option maxHeartbeats 0 in
theorem cChain_ok : chainCheck 24 tabC cChain = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem eChain_ok : chainCheck 24 tabE eChain = true := by decide +kernel
theorem zChain_ok : chainCheck 6 tabZ zChain = true := by decide +kernel

/-- Sum over levels of the longest word of the level. -/
def boundOf (ls : List Level) : ℕ :=
  (ls.map fun l => (l.es.map fun e => e.w.length).foldr max 0).sum

theorem cChain_bound : boundOf cChain = 170 := by decide +kernel
theorem eChain_bound : boundOf eChain = 220 := by decide +kernel
theorem zChain_bound : boundOf zChain = 16 := by decide +kernel

/-- Each word of the chain is even and trivial on the listed other pieces. -/
def pureOK (others : List (ℕ × List Tb)) (ls : List Level) : Bool :=
  (gensOf ls).all fun e =>
    evenS e.w && others.all fun o => tbOf o.1 (tableOf o.2) e.w == idT o.1

theorem cChain_pure : pureOK [(24, tabE), (6, tabZ)] cChain = true := by decide +kernel
theorem eChain_pure : pureOK [(24, tabC), (6, tabZ)] eChain = true := by decide +kernel
theorem zChain_pure : pureOK [(24, tabC), (24, tabE)] zChain = true := by decide +kernel

end RubiksGN
