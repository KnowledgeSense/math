import AperyMoments.CorrectionUniformBound

noncomputable section
open Set MeasureTheory Filter
namespace AperyMoments

def ellipticRayKernel (q : ℂ) (t : ℝ) : ℂ := complexEllipticK ((q * (t : ℂ)) ^ 2)

theorem ellipticRay_parameter_mem {q : ℂ} (hq : q.im < 0) {t : ℝ} (ht : 0 ≤ t) :
    (q * (t : ℂ)) ^ 2 ∈ ellipticDomain := by
  rcases ht.eq_or_lt with h | h
  · subst t
    norm_num [ellipticDomain]
  · apply lower_square_mem_ellipticDomain
    simpa using mul_neg_of_neg_of_pos hq h

theorem ellipticRay_continuousOn {q : ℂ} (hq : q.im < 0) :
    ContinuousOn (ellipticRayKernel q) (Ici 0) :=
  complexEllipticK_continuousOn.comp (by fun_prop)
    (fun _ ht => ellipticRay_parameter_mem hq ht)

theorem ellipticRay_integrable {q : ℂ} (hq : q.im < 0) {L : ℝ} (hL : 0 ≤ L) :
    IntervalIntegrable (ellipticRayKernel q) volume 0 L := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hL]
  exact (ellipticRay_continuousOn hq).mono (fun _ ht => ht.1)

theorem ellipticRay_parameter_norm {q : ℂ} (hq : ‖q‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(q * (t : ℂ)) ^ 2‖ = t ^ 2 := by
  simp only [norm_pow, norm_mul, hq, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]

theorem ellipticRay_mild_bound {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (hne : t ≠ 1) :
    ‖ellipticRayKernel q t‖ ≤ 8 * ‖t - 1‖ ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
  have hsq : ‖(q * (t : ℂ)) ^ 2‖ ≠ 1 := by
    rw [ellipticRay_parameter_norm hn ht]
    intro h
    exact hne (by nlinarith)
  have h := complexEllipticK_radial_mild_bound (ellipticRay_parameter_mem hq ht) hsq
  rw [ellipticRay_parameter_norm hn ht] at h
  have hp := Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne)))
    (one_sub_square_abs_bound ht) (by norm_num : -(1 / 16 : ℝ) ≤ 0)
  have he : |1 - t| = ‖t - 1‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
  rw [he] at hp
  unfold ellipticRayKernel
  linarith

def ellipticRaySmallBound : ℝ :=
  8 * (∫ t in (0 : ℝ)..2, ‖t - 1‖ ^ (-(1 / 16 : ℝ))) + Real.pi

theorem ellipticRay_small_integrable :
    IntervalIntegrable (fun t : ℝ => ‖t - 1‖ ^ (-(1 / 16 : ℝ))) volume 0 2 := by
  have h := (norm_rpow_intervalIntegrable (by norm_num : (1 / 16 : ℝ) < 1) (-1) 1).comp_sub_right 1
  convert h using 1 <;> norm_num

theorem ellipticRaySmallBound_nonneg : 0 ≤ ellipticRaySmallBound := by
  unfold ellipticRaySmallBound
  have h : 0 ≤ ∫ t in (0 : ℝ)..2, ‖t - 1‖ ^ (-(1 / 16 : ℝ)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    exact Real.rpow_nonneg (norm_nonneg _) _
  positivity

theorem ellipticRay_integral_small_bound {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1) :
    (∫ t in (0 : ℝ)..2, ‖ellipticRayKernel q t‖) ≤ ellipticRaySmallBound := by
  have hi := IntervalIntegrable.add (IntervalIntegrable.const_mul ellipticRay_small_integrable 8)
    (intervalIntegrable_const (c := Real.pi / 2))
  calc
    _ ≤ ∫ t in (0 : ℝ)..2, 8 * ‖t - 1‖ ^ (-(1 / 16 : ℝ)) + Real.pi / 2 := by
      apply intervalIntegral.integral_mono_ae_restrict (by norm_num)
        (ellipticRay_integrable hq (by norm_num : (0 : ℝ) ≤ 2)).norm hi
      have he : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
        apply ae_iff.mpr
        simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (1 : ℝ) : volume {(1 : ℝ)} = 0)
      filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Icc] with t ht hm
      exact ellipticRay_mild_bound hq hn hm.1 ht
    _ = _ := by
      rw [intervalIntegral.integral_add (IntervalIntegrable.const_mul ellipticRay_small_integrable 8) intervalIntegrable_const,
        intervalIntegral.integral_const_mul]
      simp [ellipticRaySmallBound]

theorem ellipticRay_large_bound {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {t : ℝ} (ht : 2 ≤ t) :
    ‖ellipticRayKernel q t‖ ≤ (ellipticK (1 / 2) + 8) * t ^ (-(7 / 8 : ℝ)) := by
  have ht0 : 0 ≤ t := by linarith
  have h := complexEllipticK_large_bound (ellipticRay_parameter_mem hq ht0)
    (by rw [ellipticRay_parameter_norm hn ht0]; nlinarith)
  rw [ellipticRay_parameter_norm hn ht0, ← Real.rpow_natCast_mul ht0] at h
  norm_num at h
  exact h

theorem ellipticRay_integral_bound {q : ℂ} (hq : q.im < 0) (hn : ‖q‖ = 1)
    {L : ℝ} (hL : 2 ≤ L) :
    (∫ t in (0 : ℝ)..L, ‖ellipticRayKernel q t‖) ≤
      ellipticRaySmallBound + 8 * (ellipticK (1 / 2) + 8) * L ^ (1 / 8 : ℝ) := by
  have hi := ellipticRay_integrable hq (by linarith : 0 ≤ L)
  have hi2 : IntervalIntegrable (fun t => ‖ellipticRayKernel q t‖) volume 2 L := by
    exact (ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le hL]
      exact (ellipticRay_continuousOn hq).norm.mono (fun t ht => by change 0 ≤ t; linarith [ht.1])))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (ellipticRay_integrable hq (by norm_num : (0 : ℝ) ≤ 2)).norm hi2]
  have hk : 0 ≤ ellipticK (1 / 2) + 8 := by linarith [ellipticK_pos (by norm_num : (1 / 2 : ℝ) < 1)]
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(7 / 8 : ℝ))) volume 2 L :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have htail : (∫ t in (2 : ℝ)..L, ‖ellipticRayKernel q t‖) ≤
      8 * (ellipticK (1 / 2) + 8) * L ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ ∫ t in (2 : ℝ)..L, (ellipticK (1 / 2) + 8) * t ^ (-(7 / 8 : ℝ)) := by
        apply intervalIntegral.integral_mono_on hL hi2 (IntervalIntegrable.const_mul hr _)
        intro t ht
        exact ellipticRay_large_bound hq hn ht.1
      _ = (ellipticK (1 / 2) + 8) * ((L ^ (1 / 8 : ℝ) - 2 ^ (1 / 8 : ℝ)) / (1 / 8)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(7 / 8 : ℝ)))]
        norm_num
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / 8 : ℝ)]
  linarith [ellipticRay_integral_small_bound hq hn]

end AperyMoments
