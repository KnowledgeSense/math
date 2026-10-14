import Dowling.DowlingInverseZCandidateKernel
import Dowling.DowlingInverseZCandidateRows

noncomputable section
namespace Dowling
open PowerSeries Finset

theorem dowlingCorrectedQuadratic_coeff_odd (c : ℝ) (j : ℕ) :
    coeff (2*j+1) (dowlingCorrectedQuadratic c)=0 := by
  rw [dowlingCorrectedQuadratic,mul_sub,mul_one,map_sub,dowlingQuadraticExp_coeff_odd]
  have he : dowlingQuadraticExp c*(C Polynomial.X*X^2)=
      C Polynomial.X*(dowlingQuadraticExp c*X^2) := by ring
  rw [he,coeff_C_mul]
  cases j with
  | zero => simp [coeff_mul_X_pow']
  | succ j =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,coeff_mul_X_pow,
      dowlingQuadraticExp_coeff_odd,mul_zero,sub_zero]

/-- Removing exactly the zero odd terms from a finite coefficient convolution. -/
theorem dowling_sum_even {R : Type*} [AddCommMonoid R] (f : ℕ→R)
    (hf : ∀ j, f (2*j+1)=0) (n : ℕ) :
    ∑ d ∈ range (n+1), f d = ∑ j ∈ range (n/2+1), f (2*j) := by
  have hinj : Function.Injective (fun j : ℕ => 2*j) := by intro a b h; dsimp at h; omega
  rw [← Finset.sum_image (fun a _ b _ h => hinj h)]
  symm
  apply Finset.sum_subset
  · intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    omega
  · intro d hd hnot
    have hd' := Finset.mem_range.mp hd
    have heven : d%2≠0 := by
      intro h
      apply hnot
      apply Finset.mem_image.mpr
      refine ⟨d/2,Finset.mem_range.mpr (by omega),by omega⟩
    rw [show d=2*(d/2)+1 by omega]
    exact hf _

theorem dowlingInverseZKernel_row (a : ℝ) (n : ℕ) :
    coeff n (dowlingInverseZKernel a n)=
      ∑ j ∈ range (n/2+1),
        Polynomial.C (dowlingQuadraticWeight (((n : ℝ)+a)/2) j)*Polynomial.X^j*
          dowlingBinomialRow a (n-2*j) := by
  have he : dowlingInverseZKernel a n=
      dowlingCorrectedQuadratic (((n : ℝ)+a)/2)*
        (dowlingBinomialSeries a*(dowlingBinomialSeries a).subst (C Polynomial.X*X)) := by
    dsimp [dowlingInverseZKernel,dowlingCorrectedQuadratic]
    ring
  rw [he,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [dowling_sum_even _ (by intro j; rw [dowlingCorrectedQuadratic_coeff_odd,zero_mul])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dowlingCorrectedQuadratic_coeff_even,dowlingBinomialProduct_coeff]

end Dowling
