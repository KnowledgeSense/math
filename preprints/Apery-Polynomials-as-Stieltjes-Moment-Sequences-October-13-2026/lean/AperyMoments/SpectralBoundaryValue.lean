import AperyMoments.SpectralBoundaryIntegrable
import AperyMoments.CorrectionRealIntegral

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem spectralBoundary_angular_integrable {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    IntervalIntegrable (fun θ => latticeLowerBoundary (a - b * Real.cos θ)) volume 0 Real.pi := by
  have hright : IntervalIntegrable
      (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • latticeLowerBoundary (a - u)) volume a b := by
    apply (arcsine_right_half_integrable_iff hl hr _).mpr
    have h := spectralBoundaryHalf_integrable hb2 hl hr (by norm_num : |(-1 : ℝ)| = 1)
    convert h using 1
    ext v
    congr 2
    ring
  have hleft' : IntervalIntegrable
      (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • latticeLowerBoundary (a + u)) volume (-a) b := by
    apply (arcsine_right_half_integrable_iff (by linarith : -b < -a) (by linarith : -a < b) _).mpr
    have h := spectralBoundaryHalf_integrable hb2 (by linarith : -b < -a) (by linarith : -a < b)
      (by norm_num : |(1 : ℝ)| = 1)
    convert h using 1
    ext v
    congr 2
    ring
  have hleft : IntervalIntegrable
      (fun u => (Real.sqrt (b ^ 2 - u ^ 2))⁻¹ • latticeLowerBoundary (a - u)) volume (-b) a := by
    have h := (IntervalIntegrable.iff_comp_neg).mp hleft'
    simpa only [neg_neg, neg_sq, ← sub_eq_add_neg] using h.symm
  apply (arcsine_integrable_iff hb (fun u => latticeLowerBoundary (a - u))).mp
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : -b ≤ b)).mp (hleft.trans hright)

theorem central_lattice_argument_bound {b a θ : ℝ} (hb : 0 ≤ b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) : |a - b * Real.cos θ| < 4 := by
  rw [abs_lt]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hb,
    mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hb]

theorem imaginary_real_quotient_re (a b : ℝ) :
    (Complex.I * (a : ℂ) / (b : ℂ)).re = 0 := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_add, sub_zero]

theorem imaginary_real_quotient_im (a b : ℝ) :
    (Complex.I * (a : ℂ) / (b : ℂ)).im = a / b := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_add, sub_zero]
  rfl

theorem latticeLowerBoundary_re (x : ℝ) : (latticeLowerBoundary x).re = latticeExpression x := by
  unfold latticeLowerBoundary
  split_ifs <;> simp only [Complex.add_re, Complex.ofReal_re, imaginary_real_quotient_re, add_zero]

theorem latticeLowerBoundary_im (a u : ℝ) :
    (latticeLowerBoundary (a - u)).im =
      ((Ioi a).indicator (fun u => ellipticK ((a - u) ^ 2 / 16)) u) / Real.pi ^ 2 := by
  unfold latticeLowerBoundary
  by_cases h : a < u
  · rw [ite_eq_left (by linarith), Set.indicator_of_mem (show u ∈ Ioi a from h)]
    simp only [Complex.add_im, Complex.ofReal_im, imaginary_real_quotient_im, zero_add]
  · rw [ite_eq_right (by linarith), Set.indicator_of_notMem (show u ∉ Ioi a from h)]
    simp

theorem spectralBoundary_value {b a : ℝ} (hb : 0 < b) (hb2 : b ≤ 2)
    (hl : -b < a) (hr : a < b) :
    (Real.pi : ℂ)⁻¹ * (∫ θ in (0 : ℝ)..Real.pi, latticeLowerBoundary (a - b * Real.cos θ)) =
      (spectralDensity b a : ℂ) + Complex.I * (centralCorrection b a : ℂ) / (Real.pi ^ 2 : ℝ) := by
  have hi := spectralBoundary_angular_integrable hb hb2 hl hr
  have hire : IntegrableOn (fun θ => latticeLowerBoundary (a - b * Real.cos θ)) (Ioc 0 Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp hi
  have hre : (∫ θ in (0 : ℝ)..Real.pi, latticeLowerBoundary (a - b * Real.cos θ)).re =
      ∫ θ in (0 : ℝ)..Real.pi, latticeDensity (a - b * Real.cos θ) := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le Real.pi_pos.le]
    change RCLike.re (∫ θ in Ioc (0 : ℝ) Real.pi, latticeLowerBoundary (a - b * Real.cos θ)) = _
    rw [← integral_re hire]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ _
    dsimp only
    rw [show RCLike.re (latticeLowerBoundary (a - b * Real.cos θ)) =
      (latticeLowerBoundary (a - b * Real.cos θ)).re from rfl, latticeLowerBoundary_re]
    exact (ite_eq_left (central_lattice_argument_bound hb.le hb2 hl hr)).symm
  have him : (∫ θ in (0 : ℝ)..Real.pi, latticeLowerBoundary (a - b * Real.cos θ)).im =
      (∫ θ in (0 : ℝ)..Real.pi,
        (Ioi a).indicator (fun u => ellipticK ((a - u) ^ 2 / 16)) (b * Real.cos θ)) / Real.pi ^ 2 := by
    rw [← intervalIntegral.integral_div, intervalIntegral.integral_of_le Real.pi_pos.le,
      intervalIntegral.integral_of_le Real.pi_pos.le]
    change RCLike.im (∫ θ in Ioc (0 : ℝ) Real.pi, latticeLowerBoundary (a - b * Real.cos θ)) = _
    rw [← integral_im hire]
    exact setIntegral_congr_fun measurableSet_Ioc fun θ _ => latticeLowerBoundary_im a (b * Real.cos θ)
  apply Complex.ext
  · rw [← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, imaginary_real_quotient_re, add_zero, hre]
    rfl
  · rw [← Complex.ofReal_inv]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im, imaginary_real_quotient_im, zero_add, him]
    rw [centralCorrection_eq_angular hb hl hr]
    ring

end AperyMoments
