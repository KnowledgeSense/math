import AperyMoments.ArcsineSplit
import AperyMoments.SpectralContinuation
import AperyMoments.LatticeBounds
import AperyMoments.ConvolutionWeight

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AperyMoments

def spectralHalfKernel (b : ℝ) (w : ℂ) (σ v : ℝ) : ℂ :=
  arcsineHalfWeight b w.re v •
    continuedLattice (((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ))

def latticeLowerBoundary (x : ℝ) : ℂ :=
  (latticeExpression x : ℂ) +
    if x < 0 then Complex.I * (ellipticK (x ^ 2 / 16) : ℂ) / (Real.pi ^ 2 : ℝ) else 0

theorem continuedLattice_real_boundary {x : ℝ} (hx : x ≠ 0) (hx4 : |x| < 4) :
    Tendsto continuedLattice (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (latticeLowerBoundary x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h := continuedLattice_negative_boundary (neg_pos.mpr hx)
      (by simpa [abs_of_neg hx] using hx4)
    have he : latticeExpression (-x) = latticeExpression x := by simp [latticeExpression]
    simpa [latticeLowerBoundary, hx, he] using h
  · simpa [latticeLowerBoundary, not_lt.mpr hx.le] using continuedLattice_positive_boundary hx

theorem arcsineHalfWeight_continuousAt {b a v : ℝ} (hl : -b < a) (hr : a < b)
    (hv : v ∈ Ioo 0 1) : ContinuousAt (fun a => arcsineHalfWeight b a v) a := by
  have ha : b - a ≠ 0 := (sub_pos.mpr hr).ne'
  have hc : b + a + (b - a) * v ≠ 0 := by nlinarith [mul_pos (sub_pos.mpr hr) hv.1]
  unfold arcsineHalfWeight
  exact (((show ContinuousAt (fun a : ℝ => b - a) a by fun_prop).mul
    ((show ContinuousAt (fun a : ℝ => b - a) a by fun_prop).rpow_const (Or.inl ha))).mul
    ((show ContinuousAt (fun a : ℝ => b + a + (b - a) * v) a by fun_prop).rpow_const
      (Or.inl hc))).mul continuousAt_const

theorem spectralHalfKernel_tendsto {b a σ v : ℝ} (hb2 : b ≤ 2) (hl : -b < a) (hr : a < b)
    (hσ : |σ| = 1) (hv : v ∈ Ioo 0 1) :
    Tendsto (fun w : ℂ => spectralHalfKernel b w σ v)
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝 (arcsineHalfWeight b a v • latticeLowerBoundary (σ * (b - a) * v))) := by
  have hxabs : |σ * (b - a) * v| = (b - a) * v := by
    rw [abs_mul, abs_mul, hσ, abs_of_pos (sub_pos.mpr hr), abs_of_pos hv.1, one_mul]
  have hx : σ * (b - a) * v ≠ 0 := abs_pos.mp (by rw [hxabs]; exact mul_pos (sub_pos.mpr hr) hv.1)
  have hx4 : |σ * (b - a) * v| < 4 := by rw [hxabs]; nlinarith [hv.2]
  have hp : Tendsto (fun w : ℂ => ((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ))
      (𝓝[{z : ℂ | z.im < 0}] ((σ * (b - a) * v : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : ContinuousAt (fun w : ℂ => ((σ * (b - w.re) * v : ℝ) : ℂ) + Complex.I * (w.im : ℂ)) (a : ℂ) := by fun_prop
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
  have hreal : Tendsto (fun w : ℂ => w.re)
      (𝓝[{z : ℂ | z.im < 0}] (a : ℂ)) (𝓝 a) :=
    Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hw := (arcsineHalfWeight_continuousAt hl hr hv).tendsto.comp hreal
  exact hw.smul ((continuedLattice_real_boundary hx hx4).comp hp)

theorem continuedSpectral_split {b : ℝ} (hb : 0 < b) {w : ℂ}
    (hw : w.im < 0) (hl : -b < w.re) (hr : w.re < b) :
    continuedSpectral b w = (Real.pi : ℂ)⁻¹ *
      ((∫ v in (0 : ℝ)..1, spectralHalfKernel b (-starRingEnd ℂ w) 1 v) +
        (∫ v in (0 : ℝ)..1, spectralHalfKernel b w (-1) v)) := by
  unfold continuedSpectral
  rw [arcsine_split hb hl hr (fun u : ℝ => continuedLattice (w - (u : ℂ)))
    ((continuedSpectral_integrand_continuous hb.le (Or.inl hw)).intervalIntegrable 0 Real.pi)]
  congr 2
  · apply intervalIntegral.integral_congr
    intro v _
    unfold spectralHalfKernel
    simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg, one_mul]
    apply congrArg (fun z : ℂ => arcsineHalfWeight b (-w.re) v • continuedLattice z)
    apply Complex.ext <;> simp
  · apply intervalIntegral.integral_congr
    intro v _
    unfold spectralHalfKernel
    apply congrArg (fun z : ℂ => arcsineHalfWeight b w.re v • continuedLattice z)
    apply Complex.ext <;> simp; ring

end AperyMoments
