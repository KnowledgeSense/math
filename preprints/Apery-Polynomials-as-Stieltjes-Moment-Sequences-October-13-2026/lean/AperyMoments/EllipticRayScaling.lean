import AperyMoments.EllipticRayIntegral

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem ellipticRay_scaled_continuousOn {q : ℂ} (hq : q.im < 0) {A : ℝ} (hA : 0 ≤ A) :
    ContinuousOn (fun v : ℝ => ‖ellipticRayKernel q (A * v)‖) (Icc 0 1) :=
  (ellipticRay_continuousOn hq).norm.comp (by fun_prop) (fun _ hv => mul_nonneg hA hv.1)

theorem ellipticRay_scaled_integral_half {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {A : ℝ} (hA : 4 ≤ A) :
    (∫ v in (0 : ℝ)..(1 / 2), ‖ellipticRayKernel q (A * v)‖) ≤
      (ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8)) * A ^ (-(7 / 8 : ℝ)) := by
  have hA0 : 0 < A := by linarith
  rw [intervalIntegral.integral_comp_mul_left (fun t => ‖ellipticRayKernel q t‖) hA0.ne']
  simp only [mul_zero, smul_eq_mul]
  have hi := ellipticRay_integral_bound hq hn (show 2 ≤ A * (1 / 2) by linarith)
  have hp : (A * (1 / 2)) ^ (1 / 8 : ℝ) ≤ A ^ (1 / 8 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hp1 : 1 ≤ A ^ (1 / 8 : ℝ) := by
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hk : 0 ≤ ellipticK (1 / 2) + 8 := by linarith [ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)]
  have hs := ellipticRaySmallBound_nonneg
  have hb : (∫ t in (0 : ℝ)..A * (1 / 2), ‖ellipticRayKernel q t‖) ≤
      (ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8)) * A ^ (1 / 8 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8 * (ellipticK (1 / 2) + 8)),
      mul_le_mul_of_nonneg_left hp1 hs]
  have he : A⁻¹ * A ^ (1 / 8 : ℝ) = A ^ (-(7 / 8 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hA0]
    norm_num
  calc
    _ ≤ A⁻¹ * ((ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8)) * A ^ (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hA0.le)
    _ = _ := by rw [mul_left_comm, he]

theorem ellipticRay_scaled_second_half {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {A v : ℝ} (hA : 4 ≤ A) (hv : 1 / 2 ≤ v) :
    ‖ellipticRayKernel q (A * v)‖ ≤ (ellipticK (1 / 2) + 8) *
      A ^ (-(7 / 8 : ℝ)) * (1 / 2 : ℝ) ^ (-(7 / 8 : ℝ)) := by
  have hA0 : 0 ≤ A := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hAv : 2 ≤ A * v := by nlinarith
  have h := ellipticRay_large_bound hq hn hAv
  rw [Real.mul_rpow hA0 hv0] at h
  have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hv
    (by norm_num : -(7 / 8 : ℝ) ≤ 0)
  have hk : 0 ≤ ellipticK (1 / 2) + 8 := by linarith [ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)]
  have hh := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hk (Real.rpow_nonneg hA0 (-(7 / 8 : ℝ))))
  nlinarith

end AperyMoments
