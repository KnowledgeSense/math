import HardCoreActivityThreshold.HigherDerivatives

namespace HardCoreActivityThreshold

set_option maxHeartbeats 2000000

noncomputable def fourthCoefficient0 (q z : ℝ) : ℝ :=
  (q-1)*(15*0.016*q^2*z^2-6*0.016*q*z^2-28*0.016*q*z-2*0.016*z^2-4*0.016*z+12*0.016+15*q^2-6*q-2)
noncomputable def fourthCoefficient1 (q z : ℝ) : ℝ :=
  2*(q-1)*(8*0.016*q^3*z^2-7*0.016*q^2*z^2-30*0.016*q^2*z+12*0.016*q*z+21*0.016*q+4*0.016*z+3*0.016+8*q^3-7*q^2)
noncomputable def fourthCoefficient2 (q z : ℝ) : ℝ :=
  -0.016*(q-1)*(32*q^3*z-28*q^2*z-45*q^2+18*q+6)
noncomputable def fourthCoefficient3 (q : ℝ) : ℝ :=
  2*0.016*q^2*(q-1)*(8*q-7)

theorem fourthNumerator_coefficients (q y : ℝ) :
    fourthNumerator q y=fourthCoefficient0 q cubicCenter+fourthCoefficient1 q cubicCenter*y+
      fourthCoefficient2 q cubicCenter*y^2+fourthCoefficient3 q*y^3 := by
  unfold fourthNumerator fourthCoefficient0 fourthCoefficient1 fourthCoefficient2 fourthCoefficient3 cubicCoefficient
  norm_num
  ring

theorem fourth_coefficient0_small (q z : ℝ) (hq : q∈Set.Icc 0 0.05)
    (hz : z∈Set.Icc 2.831082494510 2.831082494515) : 2.0931<fourthCoefficient0 q z := by
  unfold fourthCoefficient0
  simp only [pow_succ,pow_zero]
  dyadic_interval +kernel [prec := 80]

theorem fourth_coefficient1_small (q z : ℝ) (hq : q∈Set.Icc 0 0.05)
    (hz : z∈Set.Icc 2.831082494510 2.831082494515) : -0.5486<fourthCoefficient1 q z := by
  unfold fourthCoefficient1
  simp only [pow_succ,pow_zero]
  dyadic_interval +kernel [prec := 80]

theorem fourth_coefficient2_small (q z : ℝ) (hq : q∈Set.Icc 0 0.05)
    (hz : z∈Set.Icc 2.831082494510 2.831082494515) : 0.0864<fourthCoefficient2 q z := by
  unfold fourthCoefficient2
  simp only [pow_succ,pow_zero]
  dyadic_interval +kernel [prec := 80]

theorem fourth_coefficient3_small (q : ℝ) (hq : q∈Set.Icc 0 0.05) : 0≤fourthCoefficient3 q := by
  have h1 : q-1≤0 := by linarith [hq.2]
  have h2 : 8*q-7≤0 := by linarith [hq.2]
  unfold fourthCoefficient3
  have hm := mul_nonneg_of_nonpos_of_nonpos h1 h2
  nlinarith [mul_nonneg (sq_nonneg q) hm]

theorem fourthNumerator_pos_small (q y : ℝ) (hq : q∈Set.Icc 0 0.05) (hy : 0≤y) :
    0<fourthNumerator q y := by
  rw [fourthNumerator_coefficients]
  have h0 := fourth_coefficient0_small q cubicCenter hq cubicCenter_tight_bounds
  have h1 := fourth_coefficient1_small q cubicCenter hq cubicCenter_tight_bounds
  have h2 := fourth_coefficient2_small q cubicCenter hq cubicCenter_tight_bounds
  have h3 := fourth_coefficient3_small q hq
  have h1y := mul_le_mul_of_nonneg_right h1.le hy
  have h2y := mul_le_mul_of_nonneg_right h2.le (sq_nonneg y)
  have h3y := mul_nonneg h3 (pow_nonneg hy 3)
  nlinarith [sq_nonneg (0.1728*y-0.5486)]

end HardCoreActivityThreshold
