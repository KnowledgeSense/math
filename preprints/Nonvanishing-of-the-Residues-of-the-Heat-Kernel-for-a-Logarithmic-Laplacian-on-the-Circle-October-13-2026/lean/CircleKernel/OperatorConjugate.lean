import CircleKernel.OperatorEigenvalues

noncomputable section
open Complex MeasureTheory
open scoped ComplexConjugate
namespace CircleKernel

theorem mode_integrand_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (fun θ:ℝ=>(1-Complex.exp (Complex.I*θ)^n)/
      (‖1-Complex.exp (Complex.I*θ)‖:ℂ)) volume 0 (2*Real.pi) := by
  have hc : Continuous (fun θ:ℝ=>∑j∈Finset.range n,halfFrequency j θ) :=
    continuous_finsetSum _ (fun j hj=>halfFrequency_continuous j)
  apply (hc.intervalIntegrable 0 (2*Real.pi)).congr_uIoo
  rw [Set.uIoo_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  intro θ hθ
  exact (mode_integrand_sum n θ hθ.1 hθ.2).symm

theorem circleOperator_conj (f : ℂ→ℂ) (z : ℂ) :
    circleOperator (fun w=>conj (f w)) z=conj (circleOperator f z) := by
  unfold circleOperator
  simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp

theorem circleOperator_conjugate_monomial (n : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    circleOperator (fun w=>conj (w^n)) z=(circleEigenvalue n:ℂ)*conj (z^n) := by
  rw [circleOperator_conj,circleOperator_monomial n z hz]
  simp

end CircleKernel
