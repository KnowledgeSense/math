import HilbertBipartite.CorrectionRecurrence
import HilbertBipartite.BinomialTransform

open Finset Polynomial
namespace HilbertBipartite

/-- The binomial-transform correction polynomial, extended to a block of size zero. -/
noncomputable def generalizedCorrection (b a : ℕ) : Polynomial ℚ :=
  binomialTransform (correctionKernel a) b

@[simp] theorem generalizedCorrection_zero (a : ℕ) : generalizedCorrection 0 a = 0 := by
  simp [generalizedCorrection]

@[simp] theorem generalizedCorrection_one (a : ℕ) : generalizedCorrection 1 a = 0 := by
  simp [generalizedCorrection, binomialTransform, sum_range_succ]

theorem generalizedCorrection_recurrence (b a : ℕ) :
    generalizedCorrection (b+1) (a+1) = generalizedCorrection (b+1) a +
      (1+X) * generalizedCorrection b (a+1) - generalizedCorrection b a := by
  unfold generalizedCorrection
  rw [binomialTransform_succ, binomialTransform_succ]
  simp_rw [correctionKernel_pascal]
  rw [binomialTransform_add, binomialTransform_mul]
  ring

theorem generalizedCorrection_base (b : ℕ) :
    generalizedCorrection (b+2) 0 = C 2 * generalizedCorrection (b+1) 0 +
      (X-1) * generalizedCorrection b 0 + C (2^b) := by
  unfold generalizedCorrection
  rw [show correctionKernel 0 = correctionKernelBase by
    funext n
    exact correctionKernel_zero_left n]
  have h0 := binomialTransform_succ correctionKernelBase b
  have h1 := binomialTransform_succ correctionKernelBase (b+1)
  have h2 := binomialTransform_succ (fun k => correctionKernelBase (k+1)) b
  simp_rw [show ∀ k : ℕ, k+1+1=k+2 by omega, correctionKernelBase_step] at h2
  rw [binomialTransform_add, binomialTransform_mul, binomialTransform_one] at h2
  rw [show b+2=b+1+1 by omega, h1, h2]
  rw [h0]
  simp only [map_ofNat]
  ring

end HilbertBipartite
