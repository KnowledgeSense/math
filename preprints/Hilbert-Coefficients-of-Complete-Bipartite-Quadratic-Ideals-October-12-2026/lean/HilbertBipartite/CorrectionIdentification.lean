import HilbertBipartite.CorrectionCandidate
import HilbertBipartite.CorrectionGeneralized
import HilbertBipartite.CorrectionFiniteBridge

open Finset Polynomial
namespace HilbertBipartite

/-- A finite recurrence characterization of the translated correction coefficients. -/
theorem correction_family_translated_coeff
    (P : ℕ → ℕ → Polynomial ℚ)
    (hzero : ∀ a, P 0 a = 0)
    (hone : ∀ a, P 1 a = 0)
    (hbase : ∀ b, P (b+2) 0 = C 2 * P (b+1) 0 + (X-1) * P b 0 + C (2^b))
    (hrec : ∀ b a, P (b+1) (a+1) = P (b+1) a + (1+X) * P b (a+1) - P b a)
    (a b d : ℕ) :
    ((P b a).comp (1+X)).coeff d = correctionCandidate a b d := by
  induction a generalizing b d with
  | zero =>
    induction b using Nat.twoStepInduction generalizing d with
    | zero => simp [hzero]
    | one => simp [hone]
    | more b hb hb1 =>
      have ht : (P (b+2) 0).comp (1+X) =
          C 2 * (P (b+1) 0).comp (1+X) +
            X * (P b 0).comp (1+X) + C (2^b) := by
        rw [hbase]
        simp only [add_comp, mul_comp, C_comp, sub_comp, X_comp, one_comp]
        ring
      rw [ht]
      cases d with
      | zero =>
        simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, add_zero, coeff_C_zero,
          hb1, correctionCandidate_base_zero]
      | succ d =>
        simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_C_succ, add_zero,
          hb, hb1, correctionCandidate_base_succ]
  | succ a ha =>
    induction b generalizing d with
    | zero => simp [hzero]
    | succ b hb =>
      have ht : (P (b+1) (a+1)).comp (1+X) = (P (b+1) a).comp (1+X) +
          C 2 * (P b (a+1)).comp (1+X) + X * (P b (a+1)).comp (1+X) -
            (P b a).comp (1+X) := by
        rw [hrec]
        simp only [sub_comp, add_comp, mul_comp, one_comp, X_comp]
        simp only [map_ofNat]
        ring
      rw [ht]
      cases d with
      | zero =>
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul_zero, add_zero,
          ha, hb, correctionCandidate_succ_zero]
      | succ d =>
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, ha, hb,
          correctionCandidate_succ_succ]

/-- The coefficient identity follows from the recurrence identification; negative
extraction indices never occur in its specified range. -/
theorem correctionTranslated_coeff_of_candidate
    (hcoeff : ∀ a b d : ℕ, 1 ≤ a →
      ((correctionPolynomial b a).comp (1+X)).coeff d = correctionCandidate a b d)
    (a b i : ℕ) (ha : 1 ≤ a) (_hi : 1 ≤ i) (hin : i < a+b) :
    (correctionTranslated a b).coeff i = -weightedCoeff (delta a i) i (a+b-i-1) := by
  by_cases hia : i ≤ a
  · rw [correctionTranslated_coeff_low a b i hia, delta_eq_zero_if_index_le a i hia]
    simp [weightedCoeff]
  · have hai : a+1 ≤ i := by omega
    have hd : i-a-1+2 ≤ b := by omega
    unfold correctionTranslated
    have he : (-X : Polynomial ℚ)^(a+1) = C ((-1 : ℚ)^(a+1)) * X^(a+1) := by
      rw [neg_pow]
      simp
    rw [he, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hai,
      hcoeff a b (i-(a+1)) ha]
    have hd' : i-(a+1)+2 ≤ b := by omega
    rw [correctionCandidate, ite_eq_left hd']
    unfold signedDelta
    rw [weightedCoeff_C_mul]
    rw [show a+(i-(a+1))+1=i by omega,
      show b-(i-(a+1))-2=a+b-i-1 by omega]
    have hs : (-1 : ℚ)^(a+1) * (-1 : ℚ)^a = -1 := by
      rw [← pow_add, show a+1+a=2*a+1 by omega, pow_succ, pow_mul]
      norm_num
    rw [← mul_assoc, hs, neg_one_mul]

theorem generalizedCorrection_translated_coeff (a b d : ℕ) :
    ((generalizedCorrection b a).comp (1+X)).coeff d = correctionCandidate a b d :=
  correction_family_translated_coeff generalizedCorrection generalizedCorrection_zero
    generalizedCorrection_one generalizedCorrection_base generalizedCorrection_recurrence a b d

theorem correctionPolynomial_eq_generalized (a b : ℕ) (ha : 1 ≤ a) :
    correctionPolynomial b a = generalizedCorrection b a :=
  correctionPolynomial_eq_binomialTransform a b ha

theorem correctionPolynomial_translated_coeff (a b d : ℕ) (ha : 1 ≤ a) :
    ((correctionPolynomial b a).comp (1+X)).coeff d = correctionCandidate a b d := by
  rw [correctionPolynomial_eq_generalized a b ha]
  exact generalizedCorrection_translated_coeff a b d

/-- Proposition (correction), for the nonnegative coefficient extraction range. -/
theorem correctionTranslated_coeff (a b i : ℕ) (ha : 1 ≤ a) (hi : 1 ≤ i)
    (hin : i < a+b) :
    (correctionTranslated a b).coeff i = -weightedCoeff (delta a i) i (a+b-i-1) :=
  correctionTranslated_coeff_of_candidate correctionPolynomial_translated_coeff a b i ha hi hin

/-- The explicit coefficient identity for the literal polynomial contribution. -/
theorem correctionNumerator_coefficient (a b i : ℕ) (ha : 1 ≤ a) (hi : 1 ≤ i)
    (hin : i < a+b) :
    (((-X)^(a+1) * (correctionPolynomial b a).comp (1+X)) : Polynomial ℚ).coeff i =
      -weightedCoeff (delta a i) i (a+b-i-1) :=
  correctionTranslated_coeff a b i ha hi hin

end HilbertBipartite
