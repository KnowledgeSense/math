import AperyMoments.EllipticComplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- A direct lower-half-plane continuation kernel. Both square-root factors have
arguments strictly below the real axis when `z.im < 0` and `t > 0`. -/
def lowerEllipticKernel (z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ 2 + z) ^ (-(1 / 2 : ℂ)) *
    (1 + z * (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ))

/-- The convergent integral intended to realize `K(1-z²)` on its lower continuation. -/
def lowerEllipticIntegral (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), lowerEllipticKernel z t

theorem lower_quadratic_bounds {z : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (him : z.im ≤ -δ) (hM : ‖z‖ ≤ M) (t : ℝ) :
    (1 + t ^ 2 ≤ (1 + (1 + M) / δ) * ‖(t : ℂ) ^ 2 + z‖) ∧
    (1 + t ^ 2 ≤ (1 + (1 + M) / δ) * ‖1 + z * (t : ℂ) ^ 2‖) := by
  have hM0 : 0 ≤ M := (norm_nonneg z).trans hM
  have hAδ : δ ≤ ‖(t : ℂ) ^ 2 + z‖ := by
    have h := Complex.abs_im_le_norm ((t : ℂ) ^ 2 + z)
    rw [← Complex.ofReal_pow] at h
    simp only [Complex.add_im, Complex.ofReal_im, zero_add] at h
    simpa only [Complex.ofReal_pow] using (by linarith : δ ≤ -z.im).trans ((neg_le_abs _).trans h)
  have hBδ : δ * t ^ 2 ≤ ‖1 + z * (t : ℂ) ^ 2‖ := by
    have h := Complex.abs_im_le_norm (1 + z * (t : ℂ) ^ 2)
    rw [← Complex.ofReal_pow] at h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h
    have hh := mul_le_mul_of_nonneg_right (show δ ≤ -z.im by linarith) (sq_nonneg t)
    exact hh.trans (by simpa only [neg_mul, Complex.ofReal_pow] using (neg_le_abs (z.im * t ^ 2)).trans h)
  have hA : t ^ 2 ≤ ‖(t : ℂ) ^ 2 + z‖ + M := by
    have h := norm_sub_le ((t : ℂ) ^ 2 + z) z
    simp only [add_sub_cancel_right, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h.trans (add_le_add le_rfl hM)
  have hB : 1 ≤ ‖1 + z * (t : ℂ) ^ 2‖ + M * t ^ 2 := by
    have h := norm_sub_le (1 + z * (t : ℂ) ^ 2) (z * (t : ℂ) ^ 2)
    simp only [add_sub_cancel_right, norm_one, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hM (sq_nonneg t)))
  constructor
  · have h := mul_le_mul_of_nonneg_left hAδ (show 0 ≤ (1 + M) / δ by positivity)
    have he : (1 + M) / δ * δ = 1 + M := div_mul_cancel₀ _ hδ.ne'
    rw [he] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hBδ (show 0 ≤ (1 + M) / δ by positivity)
    have he : (1 + M) / δ * (δ * t ^ 2) = (1 + M) * t ^ 2 := by field_simp [hδ.ne']
    rw [he] at h
    nlinarith

theorem lowerEllipticKernel_bound {z : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (him : z.im ≤ -δ) (hM : ‖z‖ ≤ M) (t : ℝ) :
    ‖lowerEllipticKernel z t‖ ≤ (1 + (1 + M) / δ) / (1 + t ^ 2) := by
  have hM0 : 0 ≤ M := (norm_nonneg z).trans hM
  let C := 1 + (1 + M) / δ
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 0 < (1 + t ^ 2) / C := by positivity
  obtain ⟨hA, hB⟩ := lower_quadratic_bounds hδ him hM t
  have ha := Real.rpow_le_rpow_of_nonpos hr ((div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hA)) (by norm_num : (-(1/2:ℝ)) ≤ 0)
  have hb := Real.rpow_le_rpow_of_nonpos hr ((div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hB)) (by norm_num : (-(1/2:ℝ)) ≤ 0)
  have hnA := Complex.norm_cpow_real ((t : ℂ)^2+z) (-(1/2:ℝ))
  have hnB := Complex.norm_cpow_real (1+z*(t : ℂ)^2) (-(1/2:ℝ))
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hnA hnB
  rw [lowerEllipticKernel, norm_mul, hnA, hnB]
  apply (mul_le_mul ha hb (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr.le _)).trans_eq
  rw [← Real.rpow_add hr, show -(1/2:ℝ) + -(1/2:ℝ) = -1 by norm_num,
    Real.rpow_neg_one, inv_div]

theorem lowerEllipticKernel_bases_mem_slitPlane {z : ℂ} (hz : z.im < 0) (t : ℝ) :
    (t : ℂ)^2+z ∈ Complex.slitPlane ∧ 1+z*(t : ℂ)^2 ∈ Complex.slitPlane := by
  constructor
  · apply Complex.mem_slitPlane_iff.mpr
    right
    rw [← Complex.ofReal_pow]
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hz.ne
  · by_cases ht : t = 0
    · subst t
      norm_num [Complex.mem_slitPlane_iff]
    · apply Complex.mem_slitPlane_iff.mpr
      right
      rw [← Complex.ofReal_pow]
      simpa only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add] using mul_ne_zero hz.ne (pow_ne_zero 2 ht)

theorem lowerEllipticKernel_continuous {z : ℂ} (hz : z.im < 0) :
    Continuous (lowerEllipticKernel z) := by
  unfold lowerEllipticKernel
  apply Continuous.mul
  · exact Continuous.cpow (by fun_prop) continuous_const
      (fun t => (lowerEllipticKernel_bases_mem_slitPlane hz t).1)
  · exact Continuous.cpow (by fun_prop) continuous_const
      (fun t => (lowerEllipticKernel_bases_mem_slitPlane hz t).2)

theorem lowerEllipticKernel_integrable {z : ℂ} (hz : z.im < 0) :
    Integrable (lowerEllipticKernel z) volume := by
  have hi := integrable_inv_one_add_sq.const_mul (1 + (1 + ‖z‖) / (-z.im))
  apply hi.mono' (lowerEllipticKernel_continuous hz).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using lowerEllipticKernel_bound (neg_pos.mpr hz) (by simp) (le_refl ‖z‖) t

def lowerEllipticKernelDerivative (z : ℂ) (t : ℝ) : ℂ :=
  (-(1 / 2 : ℂ)) * lowerEllipticKernel z t *
    (((t : ℂ)^2+z)⁻¹ + (t : ℂ)^2 * (1+z*(t : ℂ)^2)⁻¹)

theorem lowerEllipticKernel_hasDerivAt {z : ℂ} (hz : z.im < 0) (t : ℝ) :
    HasDerivAt (fun z => lowerEllipticKernel z t) (lowerEllipticKernelDerivative z t) z := by
  obtain ⟨hA, hB⟩ := lowerEllipticKernel_bases_mem_slitPlane hz t
  have ha := ((hasDerivAt_const z ((t : ℂ)^2)).add (hasDerivAt_id z)).cpow_const
    (c := -(1/2:ℂ)) hA
  have hb := (((hasDerivAt_id z).mul_const ((t : ℂ)^2)).const_add 1).cpow_const
    (c := -(1/2:ℂ)) hB
  convert ha.mul hb using 1
  · rfl
  · simp only [lowerEllipticKernelDerivative, lowerEllipticKernel, Pi.add_apply, id_eq, zero_add, one_mul, mul_one]
    rw [Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hA),
      Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hB)]
    simp only [Complex.cpow_one, div_eq_mul_inv]
    ring

theorem lowerEllipticKernelDerivative_continuous {z : ℂ} (hz : z.im < 0) :
    Continuous (lowerEllipticKernelDerivative z) := by
  unfold lowerEllipticKernelDerivative
  apply Continuous.mul
  · exact continuous_const.mul (lowerEllipticKernel_continuous hz)
  · apply Continuous.add
    · exact Continuous.inv₀ (by fun_prop)
        (fun t => Complex.slitPlane_ne_zero (lowerEllipticKernel_bases_mem_slitPlane hz t).1)
    · apply Continuous.mul (by fun_prop)
      exact Continuous.inv₀ (by fun_prop)
        (fun t => Complex.slitPlane_ne_zero (lowerEllipticKernel_bases_mem_slitPlane hz t).2)

theorem lowerEllipticKernelDerivative_bound {z : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (him : z.im ≤ -δ) (hM : ‖z‖ ≤ M) (t : ℝ) :
    ‖lowerEllipticKernelDerivative z t‖ ≤ (1 + (1 + M) / δ) ^ 2 / (1 + t ^ 2) := by
  have hz : z.im < 0 := lt_of_le_of_lt him (neg_neg_of_pos hδ)
  let C := 1 + (1 + M) / δ
  have hM0 : 0 ≤ M := (norm_nonneg z).trans hM
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨hA, hB⟩ := lower_quadratic_bounds hδ him hM t
  obtain ⟨hAs, hBs⟩ := lowerEllipticKernel_bases_mem_slitPlane hz t
  have ha : ‖((t : ℂ)^2+z)⁻¹‖ ≤ C := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hAs))]
    nlinarith [sq_nonneg t]
  have hb : ‖(t : ℂ)^2 * (1+z*(t : ℂ)^2)⁻¹‖ ≤ C := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_inv,
      ← div_eq_mul_inv, div_le_iff₀ (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hBs))]
    nlinarith [sq_nonneg t]
  have hs := (norm_add_le (((t : ℂ)^2+z)⁻¹) ((t : ℂ)^2 * (1+z*(t : ℂ)^2)⁻¹)).trans
    (add_le_add ha hb)
  have hk := lowerEllipticKernel_bound hδ him hM t
  change ‖lowerEllipticKernelDerivative z t‖ ≤ C ^ 2 / (1 + t ^ 2)
  rw [lowerEllipticKernelDerivative, norm_mul, norm_mul]
  have hp : ‖(-(1 / 2 : ℂ))‖ = (1 / 2 : ℝ) := by norm_num
  rw [hp]
  calc
    _ ≤ (1 / 2 : ℝ) * ‖lowerEllipticKernel z t‖ * (C + C) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = C * ‖lowerEllipticKernel z t‖ := by ring
    _ ≤ C * (C / (1 + t ^ 2)) := mul_le_mul_of_nonneg_left hk hC
    _ = C ^ 2 / (1 + t ^ 2) := by ring

theorem lowerEllipticIntegral_differentiableAt {z : ℂ} (hz : z.im < 0) :
    DifferentiableAt ℂ lowerEllipticIntegral z := by
  let δ := -z.im / 2
  let M := ‖z‖ + δ
  let C := 1 + (1 + M) / δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hnear : ∀ w ∈ Metric.ball z δ, w.im ≤ -δ ∧ ‖w‖ ≤ M := by
    intro w hw
    have hd : ‖w - z‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hi := (le_abs_self (w.im - z.im)).trans (Complex.abs_im_le_norm (w-z))
    have hn : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w-z) z
    constructor
    · dsimp [δ] at hd ⊢
      linarith
    · dsimp [M]
      linarith
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := lowerEllipticKernel) (F' := lowerEllipticKernelDerivative)
    (μ := volume.restrict (Ioi (0:ℝ))) (bound := fun t => C ^ 2 / (1+t^2))
    (s := Metric.ball z δ) (Metric.ball_mem_nhds z hδ)
    (by
      filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
      exact (lowerEllipticKernel_continuous
        (lt_of_le_of_lt (hnear w hw).1 (neg_neg_of_pos hδ))).aestronglyMeasurable)
    (lowerEllipticKernel_integrable hz).integrableOn
    (lowerEllipticKernelDerivative_continuous hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t w hw =>
      lowerEllipticKernelDerivative_bound hδ (hnear w hw).1 (hnear w hw).2 t)
    (by
      change IntegrableOn (fun t : ℝ => C ^ 2 / (1 + t ^ 2)) (Ioi 0) volume
      simpa only [div_eq_mul_inv] using
        ((integrable_inv_one_add_sq.const_mul (C^2)).integrableOn :
          IntegrableOn (fun t : ℝ => C ^ 2 * (1 + t ^ 2)⁻¹) (Ioi 0) volume))
    (Filter.Eventually.of_forall fun t w hw => lowerEllipticKernel_hasDerivAt
      (lt_of_le_of_lt (hnear w hw).1 (neg_neg_of_pos hδ)) t)
  exact hd.2.differentiableAt

theorem lowerEllipticIntegral_analyticOnNhd :
    AnalyticOnNhd ℂ lowerEllipticIntegral {z : ℂ | z.im < 0} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt Complex.continuous_im continuous_const)
  intro z hz
  exact (lowerEllipticIntegral_differentiableAt hz).differentiableWithinAt

end AperyMoments
