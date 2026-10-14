import CircleKernel.FourierIntegral

noncomputable section
open Complex MeasureTheory
namespace CircleKernel

/-- The literal circle integral operator has the claimed Fourier eigenvalue;
no spectral identity is assumed. -/
theorem circleOperator_monomial (n : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    circleOperator (fun w=>w^n) z=(circleEigenvalue n:ℂ)*z^n := by
  have hden (θ : ℝ) : ‖z-z*Complex.exp (Complex.I*θ)‖=‖1-Complex.exp (Complex.I*θ)‖ := by
    rw [show z-z*Complex.exp (Complex.I*θ)=z*(1-Complex.exp (Complex.I*θ)) by ring,
      norm_mul,hz,one_mul]
  unfold circleOperator
  simp_rw [hden,mul_pow]
  calc
    _ = ∫θ:ℝ in 0..2*Real.pi,z^n*((1-Complex.exp (Complex.I*θ)^n)/
        (‖1-Complex.exp (Complex.I*θ)‖:ℂ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_mode_at_one]
      ring

end CircleKernel
