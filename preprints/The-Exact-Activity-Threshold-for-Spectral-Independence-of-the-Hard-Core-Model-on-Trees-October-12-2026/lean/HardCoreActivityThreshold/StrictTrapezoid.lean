import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import HardCoreActivityThreshold.CubicPotential
import Mathlib.Tactic.FunProp

namespace HardCoreActivityThreshold

open Set intervalIntegral

set_option maxHeartbeats 1000000

noncomputable def chord (f : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  f a+(t-a)*(f b-f a)/(b-a)

theorem convex_le_chord {f : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : ConvexOn ℝ (Icc a b) f) (t : ℝ) (ht : t∈Icc a b) : f t≤chord f a b t := by
  have hd : 0<b-a := sub_pos.mpr hab
  have ha : 0≤(b-t)/(b-a) := div_nonneg (sub_nonneg.mpr ht.2) hd.le
  have hb : 0≤(t-a)/(b-a) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hs : (b-t)/(b-a)+(t-a)/(b-a)=1 := by field_simp; ring
  have h := hf.2 ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ ha hb hs
  simp only [smul_eq_mul] at h
  have he : (b-t)/(b-a)*a+(t-a)/(b-a)*b=t := by field_simp; ring
  rw [he] at h
  convert h using 1; unfold chord; field_simp; ring

theorem strictConvex_midpoint_lt_chord {f : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : StrictConvexOn ℝ (Icc a b) f) : f ((a+b)/2)<chord f a b ((a+b)/2) := by
  have h := hf.2 ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab.ne
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)<1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have he : (1/2 : ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [he] at h
  have hd : b-a≠0 := sub_ne_zero.mpr hab.ne'
  convert h using 1; unfold chord; field_simp; ring

theorem integral_chord (f : ℝ → ℝ) {a b : ℝ} (hab : a<b) :
    (∫t in a..b,chord f a b t)=(b-a)*(f a+f b)/2 := by
  let F : ℝ → ℝ := fun t => f a*t+(t-a)^2*(f b-f a)/(2*(b-a))
  have hd : ∀t,HasDerivAt F (chord f a b t) t := by
    intro t
    convert ((hasDerivAt_id t).const_mul (f a)).add
      ((((hasDerivAt_id t).sub_const a).pow 2).mul_const (f b-f a) |>.div_const (2*(b-a))) using 1
    · rfl
    · unfold chord
      dsimp
      have hn : b-a≠0 := sub_ne_zero.mpr hab.ne'
      field_simp
  have hc : Continuous (chord f a b) := by unfold chord; fun_prop
  have h := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable a b)
  rw [h]
  dsimp [F]
  have hn : b-a≠0 := sub_ne_zero.mpr hab.ne'
  field_simp
  ring

theorem strict_trapezoid {f : ℝ → ℝ} {a b : ℝ} (hab : a<b)
    (hf : StrictConvexOn ℝ (Icc a b) f) (hc : ContinuousOn f (Icc a b)) :
    (∫t in a..b,f t)<(b-a)*(f a+f b)/2 := by
  have hg : ContinuousOn (chord f a b) (Icc a b) := by
    apply Continuous.continuousOn
    unfold chord
    fun_prop
  have hlt := integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab hc hg
    (fun t ht => convex_le_chord hab hf.convexOn t ⟨ht.1.le,ht.2⟩)
    ⟨(a+b)/2,⟨by linarith,by linarith⟩,strictConvex_midpoint_lt_chord hab hf⟩
  rwa [integral_chord f hab] at hlt

end HardCoreActivityThreshold
