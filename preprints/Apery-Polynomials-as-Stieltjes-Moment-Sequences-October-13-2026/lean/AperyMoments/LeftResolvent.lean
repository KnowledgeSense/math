import AperyMoments.ReciprocalResolvent
import AperyMoments.CauchySymmetry

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace AperyMoments

def leftSqrt (s : ℂ) : ℂ := Complex.I * Complex.sqrt (-s)
def leftReciprocalMap (α : ℝ) (s : ℂ) : ℂ := leftSqrt s + (α : ℂ) / leftSqrt s
def leftResolvent (α : ℝ) (s : ℂ) : ℂ :=
  continuedCauchy (2 * Real.sqrt α) (leftReciprocalMap α s) / leftSqrt s

theorem leftSqrt_eq_upper {s : ℂ} (hs : 0 < s.im) : leftSqrt s = Complex.sqrt s := by
  have hn : (-s).im < 0 := by simpa using neg_neg_of_pos hs
  apply Complex.ext
  · simp only [leftSqrt, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt hn,
      Complex.cpow_inv_two_re, norm_neg, Complex.neg_re, neg_neg]
    congr 2
    ring
  · simp only [leftSqrt, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, Complex.sqrt, Complex.cpow_inv_two_re,
      Complex.cpow_inv_two_im_eq_sqrt hs.le, norm_neg, Complex.neg_re, sub_eq_add_neg]

theorem leftResolvent_eq_upper (α : ℝ) {s : ℂ} (hs : 0 < s.im) :
    leftResolvent α s = reciprocalResolvent α s := by
  simp only [leftResolvent, reciprocalResolvent, leftReciprocalMap, reciprocalMap, leftSqrt_eq_upper hs]

theorem leftSqrt_ofReal {x : ℝ} (hx : x < 0) : leftSqrt (x : ℂ) =
    Complex.I * (Real.sqrt (-x) : ℂ) := by
  rw [leftSqrt, ← Complex.ofReal_neg]
  congr 1
  apply Complex.ext
  · exact Complex.re_sqrt_ofReal
  · simp [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt, abs_of_neg hx]

theorem leftSqrt_differentiableAt {s : ℂ} (hs : s.re < 0) :
    DifferentiableAt ℂ leftSqrt s := by
  have hsl : -s ∈ Complex.slitPlane := Or.inl (by simpa using neg_pos.mpr hs)
  exact ((Complex.differentiableAt_sqrt hsl).comp s (differentiableAt_id.neg)).const_mul Complex.I

theorem leftSqrt_ne_zero {s : ℂ} (hs : s.re < 0) : leftSqrt s ≠ 0 := by
  apply mul_ne_zero Complex.I_ne_zero
  unfold Complex.sqrt
  apply Complex.cpow_ne_zero_iff.mpr
  left
  intro he
  have hre := congrArg Complex.re he
  simp only [Complex.neg_re, Complex.zero_re] at hre
  linarith

theorem leftReciprocalMap_ofReal (α : ℝ) {x : ℝ} (hx : x < 0) :
    leftReciprocalMap α (x : ℂ) =
      Complex.I * ((Real.sqrt (-x) - α / Real.sqrt (-x) : ℝ) : ℂ) := by
  have hn : (Real.sqrt (-x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr hx)))
  rw [leftReciprocalMap, leftSqrt_ofReal hx]
  push_cast
  field_simp
  linear_combination (α : ℂ) * Complex.I_sq

theorem leftReciprocalMap_mem_domain {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : x < 0) :
    leftReciprocalMap α (x : ℂ) ∈ continuedCauchyDomain (2 * Real.sqrt α) := by
  rw [leftReciprocalMap_ofReal α hx]
  right
  simpa using (show 0 < 2 * Real.sqrt α by positivity)

theorem leftResolvent_differentiableAt_real {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : x < 0) : DifferentiableAt ℂ (leftResolvent α) (x : ℂ) := by
  have hb : 0 < 2 * Real.sqrt α := by positivity
  have hb2 : 2 * Real.sqrt α ≤ 2 := by
    have hh : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    linarith
  have hs : (x : ℂ).re < 0 := hx
  have hq := leftSqrt_differentiableAt hs
  have hn := leftSqrt_ne_zero hs
  have hr : DifferentiableAt ℂ (leftReciprocalMap α) (x : ℂ) :=
    hq.add ((differentiableAt_const (α : ℂ)).div hq hn)
  exact (((continuedCauchy_analyticOnNhd hb hb2 _ (leftReciprocalMap_mem_domain hα hx)).differentiableAt).comp
    (x : ℂ) hr).div hq hn

theorem leftResolvent_real {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {x : ℝ} (hx : x < 0) : (leftResolvent α (x : ℂ)).im = 0 := by
  have hb : 0 < 2 * Real.sqrt α := by positivity
  have hb2 : 2 * Real.sqrt α ≤ 2 := by
    have hh : Real.sqrt α ≤ 1 := Real.sqrt_le_one.mpr hα1
    linarith
  unfold leftResolvent
  rw [leftReciprocalMap_ofReal α hx, leftSqrt_ofReal hx]
  have hc := continuedCauchy_imaginary hb hb2 (Real.sqrt (-x) - α / Real.sqrt (-x))
  push_cast at hc
  simp [Complex.div_im, hc]

end AperyMoments
