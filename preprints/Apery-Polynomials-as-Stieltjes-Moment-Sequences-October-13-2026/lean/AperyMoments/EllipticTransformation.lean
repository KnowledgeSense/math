import AperyMoments.EllipticReal

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- The real complementary-angle transformation, with the parameter convention fixed. -/
theorem ellipticK_parameter_transform {m : ℝ} (hm : m < 1) :
    ellipticK m = (1 - m) ^ (-(1 / 2 : ℝ)) * ellipticK (m / (m - 1)) := by
  have hm1 : m - 1 < 0 := by linarith
  have hparam : m / (m - 1) < 1 := (div_lt_one_of_neg hm1).mpr (by linarith)
  have hswap := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)))
    (a := 0) (b := Real.pi / 2) (Real.pi / 2)
  simp only [sub_self, sub_zero] at hswap
  unfold ellipticK
  rw [← hswap, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [Real.sin_pi_div_two_sub]
  have he : 1 - m * Real.cos θ ^ 2 =
      (1 - m) * (1 - (m / (m - 1)) * Real.sin θ ^ 2) := by
    have htrig := Real.sin_sq_add_cos_sq θ
    have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith
    rw [hc]
    field_simp [hm1.ne]
    ring
  rw [he, Real.mul_rpow (by linarith) (ellipticK_base_pos hparam θ).le]

end AperyMoments
