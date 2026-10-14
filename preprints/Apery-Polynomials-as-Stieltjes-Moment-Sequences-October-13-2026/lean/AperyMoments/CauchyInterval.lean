import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AperyMoments

def cauchyInterval (a b : ℝ) (z : ℂ) : ℂ := ∫ t in a..b, (z-(t:ℂ))⁻¹

theorem cauchyInterval_eq_log (a b : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    cauchyInterval a b z = Complex.log (z-a)-Complex.log (z-b) := by
  have hn (t : ℝ) : z-(t:ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
    exact hz this
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -Complex.log (z-s)) (z-t)⁻¹ t := by
    have hs : z-(t:ℂ) ∈ Complex.slitPlane := by
      right
      simpa using hz
    have h := ((Complex.hasDerivAt_log hs).comp (t:ℂ)
      ((hasDerivAt_id (t:ℂ)).const_sub z)).neg
    simpa using h.comp_ofReal
  have hc : Continuous (fun t : ℝ => (z-(t:ℂ))⁻¹) :=
    (continuous_const.sub Complex.continuous_ofReal).inv₀ hn
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable a b)
  simpa only [cauchyInterval, neg_sub_neg] using h

theorem tendsto_log_shift_upper (b x : ℝ) (hxb : x < b) :
    Tendsto (fun z : ℂ => Complex.log (z-b))
      (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ))
      (𝓝 ((Real.log (b-x) : ℂ) + Real.pi*Complex.I)) := by
  have hs : Tendsto (fun z : ℂ => z-b)
      (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ))
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((x-b:ℝ):ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_sub, Pi.sub_apply, id_eq] using
        ((show Continuous (fun z : ℂ => z-b) by fun_prop).tendsto (x:ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using le_of_lt hz
  have h := (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := ((x-b:ℝ):ℂ)) (by simpa using sub_neg.mpr hxb) (by simp)).comp hs
  have he : ‖((x-b:ℝ):ℂ)‖=b-x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxb)]
    ring
  simpa only [he, Function.comp_def] using h

theorem tendsto_log_shift_lower (b x : ℝ) (hxb : x < b) :
    Tendsto (fun z : ℂ => Complex.log (z-b))
      (𝓝[{z : ℂ | z.im < 0}] (x:ℂ))
      (𝓝 ((Real.log (b-x) : ℂ) - Real.pi*Complex.I)) := by
  have hs : Tendsto (fun z : ℂ => z-b)
      (𝓝[{z : ℂ | z.im < 0}] (x:ℂ))
      (𝓝[{z : ℂ | z.im < 0}] ((x-b:ℝ):ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Complex.ofReal_sub, Pi.sub_apply, id_eq] using
        ((show Continuous (fun z : ℂ => z-b) by fun_prop).tendsto (x:ℂ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have h := (Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (z := ((x-b:ℝ):ℂ)) (by simpa using sub_neg.mpr hxb) (by simp)).comp hs
  have he : ‖((x-b:ℝ):ℂ)‖=b-x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxb)]
    ring
  simpa only [he, Function.comp_def] using h

theorem tendsto_log_shift_positive (a x : ℝ) (hax : a < x) :
    Tendsto (fun z : ℂ => Complex.log (z-a)) (𝓝 (x:ℂ))
      (𝓝 (Real.log (x-a) : ℂ)) := by
  have hs : (x:ℂ)-a ∈ Complex.slitPlane := by
    left
    simpa using sub_pos.mpr hax
  have h := (Complex.hasDerivAt_log hs).continuousAt.tendsto.comp
    ((show Continuous (fun z : ℂ => z-a) by fun_prop).tendsto (x:ℂ))
  simpa only [Function.comp_def, ← Complex.ofReal_sub,
    ← Complex.ofReal_log (le_of_lt (sub_pos.mpr hax))] using h

/-- The upper boundary value is unrestricted within the open upper half-plane. -/
theorem cauchyInterval_tendsto_upper (a b x : ℝ) (hax : a < x) (hxb : x < b) :
    Tendsto (cauchyInterval a b) (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ))
      (𝓝 ((Real.log (x-a) : ℂ)-(Real.log (b-x) : ℂ)-Real.pi*Complex.I)) := by
  have h := ((tendsto_log_shift_positive a x hax).mono_left nhdsWithin_le_nhds).sub
    (tendsto_log_shift_upper b x hxb)
  have he : (fun z : ℂ => Complex.log (z-a)-Complex.log (z-b)) =ᶠ[
      𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)] cauchyInterval a b := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (cauchyInterval_eq_log a b (ne_of_gt hz)).symm
  simpa only [sub_add_eq_sub_sub] using h.congr' he

/-- The lower boundary value is unrestricted within the open lower half-plane. -/
theorem cauchyInterval_tendsto_lower (a b x : ℝ) (hax : a < x) (hxb : x < b) :
    Tendsto (cauchyInterval a b) (𝓝[{z : ℂ | z.im < 0}] (x:ℂ))
      (𝓝 ((Real.log (x-a) : ℂ)-(Real.log (b-x) : ℂ)+Real.pi*Complex.I)) := by
  have h := ((tendsto_log_shift_positive a x hax).mono_left nhdsWithin_le_nhds).sub
    (tendsto_log_shift_lower b x hxb)
  have he : (fun z : ℂ => Complex.log (z-a)-Complex.log (z-b)) =ᶠ[
      𝓝[{z : ℂ | z.im < 0}] (x:ℂ)] cauchyInterval a b := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (cauchyInterval_eq_log a b (ne_of_lt hz)).symm
  simpa only [sub_sub_eq_add_sub, sub_add_eq_add_sub] using h.congr' he

end AperyMoments
