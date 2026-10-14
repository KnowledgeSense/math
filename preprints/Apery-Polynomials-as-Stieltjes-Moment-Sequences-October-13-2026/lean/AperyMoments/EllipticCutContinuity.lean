import AperyMoments.LowerEllipticRight
import AperyMoments.EllipticConjugation
import Mathlib.Analysis.Complex.SqrtDeriv

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

theorem ellipticKernel_bases_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) (t : ℝ) :
    (t : ℂ) ^ 2 + z ∈ Complex.slitPlane ∧ 1 + z * (t : ℂ) ^ 2 ∈ Complex.slitPlane := by
  rcases Complex.mem_slitPlane_iff.mp hz with hre | him
  · exact rightEllipticKernel_bases_mem_slitPlane hre t
  constructor
  · apply Complex.mem_slitPlane_iff.mpr
    right
    rw [← Complex.ofReal_pow]
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using him
  · by_cases ht : t = 0
    · subst t
      norm_num [Complex.mem_slitPlane_iff]
    · apply Complex.mem_slitPlane_iff.mpr
      right
      rw [← Complex.ofReal_pow]
      simpa only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add] using mul_ne_zero him (pow_ne_zero 2 ht)

theorem halfEllipticIntegral_continuousOn_slitPlane :
    ContinuousOn halfEllipticIntegral Complex.slitPlane := by
  rw [continuousOn_iff_continuous_domRestrict]
  unfold halfEllipticIntegral
  apply Continuous.mul continuous_const
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold lowerEllipticKernel
  apply Continuous.mul
  · exact Continuous.cpow (by fun_prop) continuous_const
      (fun p => (ellipticKernel_bases_mem_slitPlane p.1.property p.2).1)
  · exact Continuous.cpow (by fun_prop) continuous_const
      (fun p => (ellipticKernel_bases_mem_slitPlane p.1.property p.2).2)

theorem halfEllipticIntegral_continuousAt_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContinuousAt halfEllipticIntegral z :=
  halfEllipticIntegral_continuousOn_slitPlane.continuousAt (Complex.isOpen_slitPlane.mem_nhds hz)

def lowerCutCoordinate (m : ℂ) : ℂ := Complex.I * Complex.sqrt (m - 1)

theorem lowerCutCoordinate_square (m : ℂ) : 1 - lowerCutCoordinate m ^ 2 = m := by
  unfold lowerCutCoordinate
  rw [mul_pow, Complex.I_sq, Complex.sqrt, Complex.cpow_ofNat_inv_pow]
  ring

theorem lowerCutCoordinate_re_pos {m : ℂ} (hm : m.im < 0) : 0 < (lowerCutCoordinate m).re := by
  have hsq : Complex.sqrt (m - 1) ^ 2 = m - 1 := by
    exact Complex.cpow_ofNat_inv_pow (m - 1) 2
  have him := congrArg Complex.im hsq
  have hre : 0 ≤ (Complex.sqrt (m - 1)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    positivity
  simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im, sub_zero] at him
  simp only [lowerCutCoordinate, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  nlinarith

theorem lowerCutCoordinate_continuousAt {m : ℝ} (hm : 1 < m) :
    ContinuousAt lowerCutCoordinate (m : ℂ) := by
  unfold lowerCutCoordinate
  apply ContinuousAt.const_mul
  apply (Complex.continuousAt_sqrt (Or.inl (by simpa using (show 0 ≤ m - 1 by linarith)))).comp
    (f := fun z : ℂ => z - 1)
  fun_prop

theorem lowerCutCoordinate_mem_slitPlane {m : ℝ} (hm : 1 < m) :
    lowerCutCoordinate (m : ℂ) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  right
  have he : (lowerCutCoordinate (m : ℂ)).im = Real.sqrt (m - 1) := by
    simp only [lowerCutCoordinate, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add]
    rw [show (m : ℂ) - 1 = ((m - 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_sqrt_ofReal]
  rw [he]
  exact (Real.sqrt_pos.2 (by linarith)).ne'

theorem complexEllipticK_lower_coordinate {m : ℂ} (hm : m.im < 0) :
    complexEllipticK m = halfEllipticIntegral (lowerCutCoordinate m) := by
  rw [← lowerEllipticIntegral_eq_half_right (lowerCutCoordinate_re_pos hm),
    lowerEllipticIntegral_right_identity (lowerCutCoordinate_re_pos hm), lowerCutCoordinate_square]

/-- A genuine continuous neighborhood coordinate for the principal lower cut. -/
theorem complexEllipticK_lower_cut_boundary {m : ℝ} (hm : 1 < m) :
    Tendsto complexEllipticK (𝓝[{z : ℂ | z.im < 0}] (m : ℂ)) (𝓝 (complexEllipticK m)) := by
  have hc := (halfEllipticIntegral_continuousAt_slitPlane
    (lowerCutCoordinate_mem_slitPlane hm)).comp (lowerCutCoordinate_continuousAt hm)
  have ht : Tendsto (fun ε : ℝ => halfEllipticIntegral
      (lowerCutCoordinate ((m : ℂ) - Complex.I * ε))) (𝓝[>] 0)
      (𝓝 (halfEllipticIntegral (lowerCutCoordinate (m : ℂ)))) := by
    apply hc.tendsto.comp
    convert (show Continuous (fun ε : ℝ => (m : ℂ) - Complex.I * ε) by
      fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp
  have he : halfEllipticIntegral (lowerCutCoordinate (m : ℂ)) = complexEllipticK m := by
    apply tendsto_nhds_unique ht
    apply (complexEllipticK_lower_cut_limit hm).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact complexEllipticK_lower_coordinate (by simpa using neg_neg_of_pos (show 0 < ε from hε))
  rw [← he]
  apply hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (complexEllipticK_lower_coordinate hz).symm

end AperyMoments
