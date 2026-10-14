import Mathlib.Data.Finset.Finsupp
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace HilbertBipartite

abbrev BlockExponent (p : Nat) := Fin p →₀ Nat
abbrev ExponentPair (p q : Nat) := BlockExponent p × BlockExponent q

def blockDegree {p : Nat} (a : BlockExponent p) : Nat := ∑ i, a i

def halfDegree {p : Nat} (a : BlockExponent p) : Nat := ∑ i, a i / 2

/-- The three inequalities to be identified with membership in the actual ideal power. -/
def PowerCriterion {p q : Nat} (s : Nat) (a : BlockExponent p) (b : BlockExponent q) : Prop :=
  2*s ≤ blockDegree a + blockDegree b ∧
  s ≤ halfDegree a + blockDegree b ∧ s ≤ halfDegree b + blockDegree a

instance {p q : Nat} (s : Nat) (a : BlockExponent p) (b : BlockExponent q) :
    Decidable (PowerCriterion s a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

noncomputable def exponentBox (p s : Nat) : Finset (BlockExponent p) :=
  (Finset.univ : Finset (Fin p)).finsupp (fun _ => Finset.range (2*s))

/-- Actual bounded exponent pairs satisfying the standard-monomial criterion.
The algebraic bridge must prove this is precisely the quotient monomial basis. -/
noncomputable def standardExponents (p q s : Nat) : Finset (ExponentPair p q) :=
  (exponentBox p s ×ˢ exponentBox q s).filter
    (fun ab => ¬ PowerCriterion s ab.1 ab.2)

/-- The finite correction sum D from equation (1.2) of the release. -/
def correction (a b s : Nat) : Nat :=
  ∑ t ∈ Finset.range (s+1), ∑ r ∈ Finset.Icc 1 (s-t),
    ∑ k ∈ Finset.Icc (t+2*r) a,
      (t+b-1).choose (b-1) * a.choose k * (s-t-r+a-1).choose (a-1)

open Polynomial in
/-- Delta from the paper; an empty index range contributes zero. -/
noncomputable def delta (m i : Nat) : Polynomial Rat :=
  ∑ j ∈ (Finset.range i).filter (m ≤ ·),
    Polynomial.C ((-1 : Rat)^j * ((i-1).choose j : Rat)) * (1 - Polynomial.X)^j

/-- The truncated binomial numerator used in the sign proof. -/
noncomputable def gPoly (m i : Nat) : Polynomial Rat :=
  Polynomial.X^(i-1) - delta m i

/-- Explicit coefficient convolution with (1-2z)^(-i-1). -/
noncomputable def weightedCoeff (P : Polynomial Rat) (i r : Nat) : Rat :=
  ∑ j ∈ Finset.range (r+1),
    P.coeff j * (2 : Rat)^(r-j) * ((r-j+i).choose i : Rat)

noncomputable def tau (m i r : Nat) : Rat := weightedCoeff (gPoly m i) i r

/-- The paper's coefficient expression, before its identification with the
Hilbert coefficients of the actual ideal. -/
noncomputable def coefficientFormula (p q i : Nat) : Rat :=
  if i = 0 then 2^(p+q)
  else if i < p+q then
    weightedCoeff (Polynomial.X^(i-1) - delta p i - delta q i) i (p+q-i-1)
  else 0

end HilbertBipartite
