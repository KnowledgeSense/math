import BoseBurton.FlagCountingCancellation
import BoseBurton.KernelCoefficients

noncomputable section
namespace BoseBurton
open Finset Polynomial Submodule Module
open scoped Classical

/-- The correction row after actual flag-pair cancellation. -/
def correctionRow (q : ℝ) (r s d : ℕ) : Polynomial ℝ :=
  ∑ i ∈ range (d+1), monomial i
    (gaussian q s (max i (d-i)) * gaussian q (r-max i (d-i)) (d-max i (d-i)))

def restrictedRankRow (q : ℝ) (r s d : ℕ) : Polynomial ℝ :=
  ∑ i ∈ range (d+1), monomial i
    (gaussian q r d * gaussian q d i -
      gaussian q s (max i (d-i)) * gaussian q (r-max i (d-i)) (d-max i (d-i)))

theorem correctionRow_coeff (q : ℝ) (r s d i : ℕ) :
    (correctionRow q r s d).coeff i = if i ≤ d then
      gaussian q s (max i (d-i)) * gaussian q (r-max i (d-i)) (d-max i (d-i)) else 0 := by
  by_cases h : i ≤ d <;> simp [correctionRow, coeff_monomial, h]

theorem restrictedRankRow_coeff (q : ℝ) (r s d i : ℕ) :
    (restrictedRankRow q r s d).coeff i = if i ≤ d then
      gaussian q r d * gaussian q d i -
        gaussian q s (max i (d-i)) * gaussian q (r-max i (d-i)) (d-max i (d-i)) else 0 := by
  by_cases h : i ≤ d <;> simp [restrictedRankRow, coeff_monomial, h]

theorem restrictedRankRow_decomposition (q : ℝ) (r s d : ℕ) :
    restrictedRankRow q r s d = C (gaussian q r d) * gaussianRow q d - correctionRow q r s d := by
  ext i
  rw [restrictedRankRow_coeff, coeff_sub, coeff_C_mul, gaussianRow_coeff, correctionRow_coeff]
  by_cases h : i ≤ d
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, gaussian_outside q d i (by omega)]
    ring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Module.Finite K V] [Finite V]

/-- The summed restricted-Z polynomial is the exact rank row, not a proposed proxy. -/
theorem summed_restrictedZ_polynomial (W : Submodule K V) (d : ℕ) :
    (∑ U : NondeletedRankSubspace W d, (restrictedZRow W U.1).map (Int.castRingHom ℝ)) =
      restrictedRankRow (Fintype.card K : ℝ) (finrank K V) (finrank K W) d := by
  ext i
  rw [finsetSum_coeff, restrictedRankRow_coeff]
  simp only [coeff_map]
  change (∑ U : NondeletedRankSubspace W d, ((restrictedZRow W U.1).coeff i : ℝ)) = _
  by_cases h : i ≤ d
  · rw [ite_eq_left h]
    exact summed_restrictedZ_coeff W d i h
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro U _
    rw [restrictedZRow_coeff, U.2.1, ite_eq_right h]
    simp

end BoseBurton
