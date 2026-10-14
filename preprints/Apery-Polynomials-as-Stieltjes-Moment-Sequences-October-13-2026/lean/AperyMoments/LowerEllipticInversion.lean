import AperyMoments.LowerEllipticLimit

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem inverse_sqrt_cpow_pos_mul {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a : ℂ) * z) ^ (-(1 / 2 : ℂ)) =
      ((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * z ^ (-(1 / 2 : ℂ)) := by
  by_cases hz : z = 0
  · subst z
    norm_num [Complex.zero_cpow]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero ha0 hz), Complex.log_ofReal_mul ha hz,
    add_mul, Complex.exp_add, Complex.ofReal_log ha.le,
    ← Complex.cpow_def_of_ne_zero ha0, ← Complex.cpow_def_of_ne_zero hz,
    inverse_sqrt_cpow_of_nonneg ha.le]

theorem lowerEllipticKernel_inversion (z : ℂ) {t : ℝ} (ht : 0 < t) :
    |-(t ^ 2)⁻¹| • lowerEllipticKernel z t⁻¹ = lowerEllipticKernel z t := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hA : ((t⁻¹ : ℝ) : ℂ) ^ 2 + z =
      (((t ^ 2)⁻¹ : ℝ) : ℂ) * (1 + z * (t : ℂ) ^ 2) := by
    push_cast
    field_simp
  have hB : 1 + z * ((t⁻¹ : ℝ) : ℂ) ^ 2 =
      (((t ^ 2)⁻¹ : ℝ) : ℂ) * ((t : ℂ) ^ 2 + z) := by
    push_cast
    field_simp
  have hpow : ((t ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = t := by
    rw [inverse_sqrt_rpow (by positivity), Real.sqrt_inv, Real.sqrt_sq ht.le, inv_inv]
  unfold lowerEllipticKernel
  rw [hA, hB, inverse_sqrt_cpow_pos_mul (by positivity),
    inverse_sqrt_cpow_pos_mul (by positivity), hpow,
    abs_neg, abs_of_pos (by positivity : 0 < (t ^ 2)⁻¹)]
  rw [Complex.real_smul]
  push_cast
  field_simp

theorem lowerEllipticKernel_integrableOn_of_first (z : ℂ)
    (hi : IntervalIntegrable (lowerEllipticKernel z) volume 0 1) :
    IntegrableOn (lowerEllipticKernel z) (Ioi (0 : ℝ)) := by
  have hinv := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (1 : ℝ)) (f := fun t : ℝ => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (ne_of_gt (by linarith [show 1 < t from ht] : 0 < t))).hasDerivWithinAt)
    (fun _ _ _ _ h => inv_injective h) (lowerEllipticKernel z)
  rw [show (fun t : ℝ => t⁻¹) '' Ioi 1 = Ioo 0 1 by
    simpa using elliptic_inversion_image (by norm_num : (0 : ℝ) < 1)] at hinv
  have hfirst := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hi
  have htail : IntegrableOn (lowerEllipticKernel z) (Ioi (1 : ℝ)) :=
    IntegrableOn.congr_fun (hinv.mp hfirst)
      (fun t ht => lowerEllipticKernel_inversion z (by linarith [show 1 < t from ht])) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hi.1.union htail

/-- Reciprocal symmetry reduces the continuation integral to a bounded interval. -/
theorem lowerEllipticIntegral_half_of_integrable {z : ℂ}
    (hi : IntegrableOn (lowerEllipticKernel z) (Ioi (0 : ℝ))) :
    lowerEllipticIntegral z = 2 * ∫ t in (0 : ℝ)..1, lowerEllipticKernel z t := by
  have he := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (1 : ℝ)) (f := fun t : ℝ => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (ne_of_gt (by linarith [show 1 < t from ht] : 0 < t))).hasDerivWithinAt)
    (fun _ _ _ _ h => inv_injective h) (lowerEllipticKernel z)
  rw [show (fun t : ℝ => t⁻¹) '' Ioi 1 = Ioo 0 1 by
    simpa using elliptic_inversion_image (by norm_num : (0 : ℝ) < 1)] at he
  have ht : (∫ t in Ioi (1 : ℝ), |-(t ^ 2)⁻¹| • lowerEllipticKernel z t⁻¹) =
      ∫ t in Ioi (1 : ℝ), lowerEllipticKernel z t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact lowerEllipticKernel_inversion z (by linarith [show 1 < t from ht])
  rw [ht, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at he
  unfold lowerEllipticIntegral
  rw [← intervalIntegral.integral_interval_add_Ioi' ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hi.mono_set Ioc_subset_Ioi_self)) (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))),
    ← he]
  ring

theorem lowerEllipticIntegral_half {z : ℂ} (hz : z.im < 0) :
    lowerEllipticIntegral z = 2 * ∫ t in (0 : ℝ)..1, lowerEllipticKernel z t :=
  lowerEllipticIntegral_half_of_integrable (lowerEllipticKernel_integrable hz).integrableOn

end AperyMoments
