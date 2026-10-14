import HardCoreActivityThreshold.GapUpper
import Mathlib.Analysis.Matrix.PosDef

/-! The actual correlation eigenvalues and the genuine heat-bath upper bound. -/
namespace HardCoreActivityThreshold
open Finset Matrix
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem correlationMatrix_isHermitian (μ : FiniteLaw (Finset V)) :
    (correlationMatrix μ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext u v
  exact correlationMatrix_symm μ v u

theorem correlationMatrix_posSemidef (μ : FiniteLaw (Finset V)) :
    (correlationMatrix μ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨correlationMatrix_isHermitian μ, ?_⟩
  intro coeff
  have h := correlation_quadratic_nonneg μ coeff
  simpa only [dotProduct, mulVec, star_trivial, mul_sum, mul_assoc] using h

noncomputable def leadingCorrelationIndex [Nonempty V] : V :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))) ⟨0, Fintype.card_pos⟩

noncomputable def largestCorrelationEigenvalue [Nonempty V] (μ : FiniteLaw (Finset V)) : ℝ :=
  (correlationMatrix_isHermitian μ).eigenvalues (leadingCorrelationIndex (V := V))

theorem correlationEigenvalue_le_largest [Nonempty V] (μ : FiniteLaw (Finset V)) (i : V) :
    (correlationMatrix_isHermitian μ).eigenvalues i ≤ largestCorrelationEigenvalue μ := by
  unfold largestCorrelationEigenvalue Matrix.IsHermitian.eigenvalues leadingCorrelationIndex
  simp only [Equiv.symm_apply_apply]
  apply Matrix.IsHermitian.eigenvalues₀_antitone
  exact Nat.zero_le _

theorem largestCorrelationEigenvalue_ge_one [Nonempty V] (μ : FiniteLaw (Finset V))
    (hvar : ∀ v, 0 < occupationVariance μ v) : 1 ≤ largestCorrelationEigenvalue μ := by
  have htrace : (correlationMatrix μ).trace = (Fintype.card V : ℝ) := by
    unfold Matrix.trace Matrix.diag
    simp_rw [correlationMatrix_diag μ _ (hvar _)]
    simp
  have hsum := sum_le_sum (s := (univ : Finset V))
    (fun i _ => correlationEigenvalue_le_largest μ i)
  have hsum_eq : (∑ i, (correlationMatrix_isHermitian μ).eigenvalues i) = (correlationMatrix μ).trace := by
    simpa using (correlationMatrix_isHermitian μ).trace_eq_sum_eigenvalues.symm
  rw [hsum_eq, htrace] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hn : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  nlinarith

theorem correlation_eigenvector_square_sum (μ : FiniteLaw (Finset V)) (i : V) :
    (∑ v, ((correlationMatrix_isHermitian μ).eigenvectorBasis i).ofLp v ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, OrthonormalBasis.norm_eq_one]
  norm_num

theorem correlation_eigenvector_quadratic (μ : FiniteLaw (Finset V)) (i : V) :
    (∑ u, ∑ v, ((correlationMatrix_isHermitian μ).eigenvectorBasis i).ofLp u *
      correlationMatrix μ u v * ((correlationMatrix_isHermitian μ).eigenvectorBasis i).ofLp v) =
      (correlationMatrix_isHermitian μ).eigenvalues i := by
  rw [Matrix.IsHermitian.eigenvalues_eq]
  simp only [dotProduct, mulVec, star_trivial, RCLike.re_to_real, mul_sum, mul_assoc]

/-- Lemma `gapupper` of the source, for the exact heat-bath transition kernel. -/
theorem heatBathGap_le_inverse_largestCorrelationEigenvalue [Nonempty V]
    (μ : FiniteLaw (Finset V)) (hvar : ∀ v, 0 < occupationVariance μ v) :
    heatBathGap μ ≤ 1 / ((Fintype.card V : ℝ) * largestCorrelationEigenvalue μ) := by
  let i := leadingCorrelationIndex (V := V)
  let coeff : V → ℝ := ((correlationMatrix_isHermitian μ).eigenvectorBasis i).ofLp
  have hq : 0 < ∑ u, ∑ v, coeff u * correlationMatrix μ u v * coeff v := by
    rw [correlation_eigenvector_quadratic]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (largestCorrelationEigenvalue_ge_one μ hvar)
  have h := heatBathGap_le_correlation_rayleigh μ coeff hvar hq
  rw [correlation_eigenvector_square_sum, correlation_eigenvector_quadratic] at h
  exact h

end HardCoreActivityThreshold
