import HankelAutomaticity.PolynomialPair
import HankelAutomaticity.ResidueData

noncomputable section
namespace HankelAutomaticity

/-- A suffix's two residues and its full finite answer function. The length
field distinguishes only zero, one, and at least two digits. -/
 @[ext] structure SuffixState (K : ℕ) where
  value : ZMod (2^K)
  power : ZMod (2^K)
  shortLength : Fin 3
  head : Bool
  parity : ZMod 2
  answers : Bool → ZMod (2^K) → ZMod (2^K) × ZMod (2^K)

 instance suffixStateFinite (K : ℕ) : Finite (SuffixState K) := by
  let : NeZero (2^K) := ⟨by positivity⟩
  exact Finite.of_injective
    (fun s : SuffixState K => (s.value, s.power, s.shortLength, s.head, s.parity, s.answers))
    (by intro s t h; cases s; cases t; simpa using h)

 def suffixAnswersStep {K : ℕ} (s : SuffixState K) (o : Bool) (q : ZMod (2^K)) :
    ZMod (2^K) × ZMod (2^K) :=
  let u := 1-2*q
  if s.shortLength.val=0 then (-q, u)
  else if s.shortLength.val=1 then
    if Bool.xor s.head o then (q*u*(3-8*q), -u^2*(1-4*q)) else (3*q-1, 2*q-1)
  else if Bool.xor s.head o then
    let p := s.answers o (2*q)
    (u^s.power.val*p.1-q*u^(s.power-1).val*p.2, u^s.power.val*p.2)
  else
    let r := if o then s.power-1-s.value else s.value
    let parity := if o then 1-s.parity else s.parity
    let sign := (-1 : ZMod (2^K))^parity.val
    let p := s.answers (!o) 1
    (sign*(u^(2*r+1).val*p.1-q*u^(2*r).val*p.2), sign*u^(2*r+1).val*p.2)

 def suffixStep {K : ℕ} (s : SuffixState K) (b : Bool) : SuffixState K where
  value := (if b then s.power else 0)+s.value
  power := 2*s.power
  shortLength := ⟨min (s.shortLength.val+1) 2, by omega⟩
  head := b
  parity := (if s.shortLength.val=0 then (if b then 1 else 0) else 0)+s.parity
  answers := suffixAnswersStep s

 def suffixSummary (K : ℕ) (w : List Bool) : SuffixState K where
  value := binaryValue w
  power := 2^w.length
  shortLength := ⟨min w.length 2, by omega⟩
  head := w.headD false
  parity := binaryValue w
  answers := fun o q => polynomialPair (twist o w) q

 def suffixStart (K : ℕ) : SuffixState K := suffixSummary K []

end HankelAutomaticity
