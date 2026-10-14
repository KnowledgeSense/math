import ASR312.Boundary
import Mathlib.RingTheory.Binomial
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

namespace ASR312

/-- Generalized integer binomial, with negative lower index interpreted as zero.
For nonnegative lower index, `Ring.choose` is the falling-factorial binomial. -/
def generalizedBinomial (u v : ℤ) : ℤ :=
  if v < 0 then 0 else Ring.choose u v.toNat

/-- The original closed formula, with its coefficientwise-finite Catalan sum.
The range `j < d` contains every potentially nonzero Catalan summand. -/
def F (r k d : ℕ) : ℤ :=
  (∑ i ∈ Finset.Icc 1 d, (2 : ℤ)^(i-1) * (k.choose i : ℤ) *
    (generalizedBinomial ((r : ℤ)-2) ((d : ℤ)-i) -
      2 * generalizedBinomial ((r : ℤ)-2) ((d : ℤ)-i-2))) + (r.choose d : ℤ) +
  (∑ j ∈ Finset.range d, (catalan (2*j) : ℤ) *
    generalizedBinomial ((r : ℤ)-1+2*j) ((d : ℤ)-1-2*j)) +
  2 * ∑ i ∈ Finset.Icc 1 d, (-1 : ℤ)^i * (r.choose (d-i) : ℤ)

/-- The requested full theorem, stated for the original extension-count objects.
No recurrence or proposed formula occurs in the definition of `S`. -/
def FullEnumeration : Prop :=
  ∀ r k d : ℕ, d ≤ r → d ≤ k → (S r k d : ℤ) = F r k d

 theorem F_zero (r k : ℕ) : F r k 0 = 1 := by
  simp [F]

 theorem enumeration_zero_defect (r k : ℕ) : (S r k 0 : ℤ) = F r k 0 := by
  rw [S_zero,F_zero]
  rfl

 theorem catalan_summand_vanishes {r d j : ℕ} (h : d ≤ j) :
    generalizedBinomial ((r : ℤ)-1+2*j) ((d : ℤ)-1-2*j) = 0 := by
  unfold generalizedBinomial
  rw [ite_eq_left]
  omega

end ASR312
