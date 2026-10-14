import HilbertBipartite.LengthConvolution
import HilbertBipartite.SquareCoefficients
import HilbertBipartite.CorrectionIdentity

open Finset Polynomial
namespace HilbertBipartite

/-- The Hilbert numerator of the actual complete-bipartite ideal. -/
noncomputable def bipartiteNumerator (p q : ℕ) : Polynomial ℚ :=
  squareNumerator (p+q) + (1-X)^(q+1)*correctionPolynomial p q +
    (1-X)^(p+1)*correctionPolynomial q p

/-- Coefficients at one, identified below with the actual quotient lengths. -/
noncomputable def hilbertCoefficient (p q i : ℕ) : ℚ :=
  ((bipartiteNumerator p q).comp (1+X)).coeff i

theorem bipartiteNumerator_translated (p q : ℕ) :
    (bipartiteNumerator p q).comp (1+X) =
      (squareNumerator (p+q)).comp (1+X) + correctionTranslated q p +
        correctionTranslated p q := by
  simp only [bipartiteNumerator, add_comp, mul_comp, pow_comp, sub_comp, one_comp, X_comp,
    correctionTranslated]
  ring

theorem hilbertCoefficient_decomposition (p q i : ℕ) :
    hilbertCoefficient p q i = (squareCoefficient (p+q) i : ℚ) +
      (correctionTranslated q p).coeff i + (correctionTranslated p q).coeff i := by
  rw [hilbertCoefficient, bipartiteNumerator_translated, coeff_add, coeff_add,
    squareNumerator_translated_coeff]

theorem hilbertCoefficient_high (p q i : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hi : p+q ≤ i) : hilbertCoefficient p q i = 0 := by
  rw [hilbertCoefficient_decomposition,
    squareCoefficient_eq_zero (p+q) i (by omega), Nat.cast_zero,
    correctionTranslated_coeff_high q p i hp (by omega),
    correctionTranslated_coeff_high p q i hq hi]
  ring

theorem bipartiteNumerator_translated_natDegree (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ((bipartiteNumerator p q).comp (1+X)).natDegree ≤ p+q-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact hilbertCoefficient_high p q i hp hq (by omega)

theorem bipartiteNumerator_convolution (p q s : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    hilbertConvolution (bipartiteNumerator p q) (p+q) (s-1) =
      ((2*s+p+q-1).choose (p+q) + correction p q s + correction q p s : ℕ) := by
  rw [bipartiteNumerator, hilbertConvolution_add, hilbertConvolution_add,
    hilbertConvolution_cancel_pow_mul _ (q+1) (p+q) (s-1) (by omega),
    hilbertConvolution_cancel_pow_mul _ (p+1) (p+q) (s-1) (by omega),
    show p+q-(q+1)=p-1 by omega, show p+q-(p+1)=q-1 by omega,
    correction_hilbertConvolution p q s hp hs, correction_hilbertConvolution q p s hq hs,
    squareNumerator_convolution]
  rw [show 2*(s-1)+(p+q)+1=2*s+p+q-1 by omega]
  push_cast
  rfl

/-- The actual composition length has the displayed Hilbert expansion for every `s ≥ 1`. -/
theorem compositionLength_hilbertExpansion (K : Type*) [Field K]
    (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    ((Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s)).toNat : ℚ) =
      ∑ i ∈ range (p+q+1), (-1 : ℚ)^i * hilbertCoefficient p q i *
        ((s+p+q-i-1).choose (p+q-i) : ℚ) := by
  rw [compositionLength_formula K p q s hp hq hs]
  simp only [ENat.toNat_natCast]
  rw [← bipartiteNumerator_convolution p q s hp hq hs]
  rw [hilbertConvolution_expansion _ _ _
    ((bipartiteNumerator_translated_natDegree p q hp hq).trans (by omega))]
  apply sum_congr rfl
  intro i _
  unfold hilbertCoefficient
  rw [show s-1+(p+q)-i=s+p+q-i-1 by omega]

/-- The leading Hilbert coefficient. -/
theorem hilbertCoefficient_zero (p q : ℕ) : hilbertCoefficient p q 0 = 2^(p+q) := by
  rw [hilbertCoefficient_decomposition, correctionTranslated_coeff_low q p 0 (by omega),
    correctionTranslated_coeff_low p q 0 (by omega), squareCoefficient_zero_index]
  simp

/-- The initial Hilbert coefficients agree with those of the square of the maximal ideal. -/
theorem hilbertCoefficient_low (p q i : ℕ) (hpq : p ≤ q) (hi : i ≤ p) :
    hilbertCoefficient p q i = 2^(p+q-2*i)*((p+q-i).choose i : ℚ) := by
  rw [hilbertCoefficient_decomposition, correctionTranslated_coeff_low q p i (by omega),
    correctionTranslated_coeff_low p q i hi, squareCoefficient]
  push_cast
  ring

theorem hilbertCoefficient_low_pos (p q i : ℕ) (hpq : p ≤ q) (hi : i ≤ p) :
    0 < hilbertCoefficient p q i := by
  rw [hilbertCoefficient_low p q i hpq hi]
  apply mul_pos (by positivity)
  exact_mod_cast Nat.choose_pos (by omega : i ≤ p+q-i)

end HilbertBipartite
