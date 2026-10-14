import EdgeColoringMixing.MarginalDistance

set_option autoImplicit false

namespace EdgeColoringMixing.WeightedInjection
open Finset Matrix

variable {d q : ℕ}

/-- The exact first moment of the deleted-cell conditional marginals. -/
theorem posterior_first_moment (μ : FiniteLaw (Injection d q)) (y : Fin d × Fin q) :
    (∑ x ∈ active μ, mean μ x.1 x.2 * posteriorMean μ x y) =
      ((d : ℝ) - 1) * mean μ y.1 y.2 := by
  classical
  have hpoint (x : Fin d × Fin q) (hx : x ∈ active μ) :
      mean μ x.1 x.2 * posteriorMean μ x y =
        mean μ x.1 x.2 * mean μ y.1 y.2 + covariance μ y x -
          if x = y then mean μ x.1 x.2 else 0 := by
    rw [posteriorMean_eq μ x y hx]
    change mean μ x.1 x.2 * (conditionalMean μ x y - if x = y then 1 else 0) = _
    rw [mul_sub, mean_mul_conditionalMean]
    split_ifs <;> ring
  have hcorrect : (∑ x ∈ active μ, if x = y then mean μ x.1 x.2 else 0) = mean μ y.1 y.2 := by
    by_cases hy : y ∈ active μ
    · simp [hy]
    · simp [hy, mean_eq_zero_of_not_active μ hy]
  calc
    _ = ∑ x ∈ active μ, (mean μ x.1 x.2 * mean μ y.1 y.2 + covariance μ y x -
          if x = y then mean μ x.1 x.2 else 0) := Finset.sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        active_mean_total, active_covariance_total, hcorrect]
      ring

/-- Matrix version of the actual posterior first-moment identity. -/
theorem posterior_diagonal_first_moment (μ : FiniteLaw (Injection d q)) :
    (∑ x ∈ active μ, mean μ x.1 x.2 • Matrix.diagonal (posteriorMean μ x)) =
      ((d : ℝ) - 1) • Matrix.diagonal (fun y => mean μ y.1 y.2) := by
  ext y z
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · simp only [hyz, ite_true]
    exact posterior_first_moment μ z
  · simp [hyz]

end EdgeColoringMixing.WeightedInjection
