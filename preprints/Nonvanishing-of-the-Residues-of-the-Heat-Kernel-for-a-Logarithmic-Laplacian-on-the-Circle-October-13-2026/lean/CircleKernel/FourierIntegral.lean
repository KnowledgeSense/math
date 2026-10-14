import CircleKernel.FourierIntegrand

noncomputable section
open Complex MeasureTheory
namespace CircleKernel

def halfFrequency (n : ℕ) (θ : ℝ) : ℂ :=
  -Complex.I*Complex.exp (((n:ℂ)+1/2)*Complex.I*θ)

theorem halfFrequency_continuous (n : ℕ) : Continuous (halfFrequency n) := by
  unfold halfFrequency
  fun_prop

theorem integral_halfFrequency (n : ℕ) :
    (∫θ:ℝ in 0..2*Real.pi,halfFrequency n θ)=(4/(2*(n:ℝ)+1):ℝ) := by
  have hn : (n:ℂ)+1/2≠0 := by
    have h : (0:ℝ)<(n:ℝ)+1/2 := by positivity
    simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr (ne_of_gt h)
  have hc : ((n:ℂ)+1/2)*Complex.I≠0 := mul_ne_zero hn Complex.I_ne_zero
  have he : Complex.exp ((((n:ℂ)+1/2)*Complex.I)*(2*Real.pi))=-1 := by
    rw [show (((n:ℂ)+1/2)*Complex.I)*(2*Real.pi)=
      (n:ℂ)*(2*Real.pi*Complex.I)+Real.pi*Complex.I by ring]
    rw [Complex.exp_add,Complex.exp_nat_mul_two_pi_mul_I,Complex.exp_pi_mul_I,one_mul]
  simp only [halfFrequency]
  rw [intervalIntegral.integral_const_mul,integral_exp_mul_complex hc]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,he]
  push_cast
  field_simp
  ring_nf

theorem mode_integrand_sum (n : ℕ) (θ : ℝ) (hθ : 0<θ) (hθπ : θ<2*Real.pi) :
    (1-Complex.exp (Complex.I*θ)^n)/(‖1-Complex.exp (Complex.I*θ)‖:ℂ)=
      ∑j∈Finset.range n,halfFrequency j θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd := mode_integrand_difference n θ hθ hθπ
    rw [Finset.sum_range_succ]
    change _=(_)+(-Complex.I*Complex.exp (((n:ℂ)+1/2)*Complex.I*θ))
    linear_combination hd+ih

theorem integral_mode_at_one (n : ℕ) :
    (∫θ:ℝ in 0..2*Real.pi,
      (1-Complex.exp (Complex.I*θ)^n)/(‖1-Complex.exp (Complex.I*θ)‖:ℂ))=
        (circleEigenvalue n:ℂ) := by
  calc
    _ = ∫θ:ℝ in 0..2*Real.pi,∑j∈Finset.range n,halfFrequency j θ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
      intro θ hθ
      exact mode_integrand_sum n θ hθ.1 hθ.2
    _ = ∑j∈Finset.range n,((4/(2*(j:ℝ)+1):ℝ):ℂ) := by
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [integral_halfFrequency]
      · intro j hj
        exact (halfFrequency_continuous j).intervalIntegrable _ _
    _ = _ := by
      simp only [circleEigenvalue,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_sum,
        Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end CircleKernel
