import AperyMoments.EllipticCutContinuity
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Set MeasureTheory
namespace AperyMoments

def correctionParameter (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  ((w - b) * (v : ℂ) / 4) ^ 2

def correctionBase (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  ((b * (1 + v) : ℝ) : ℂ) + w * ((1 - v : ℝ) : ℂ)

def correctionRegular (b : ℝ) (w : ℂ) (v : ℝ) : ℂ :=
  complexEllipticK (correctionParameter b w v) * correctionBase b w v ^ (-(1 / 2 : ℂ))

def correctionWeight (v : ℝ) : ℝ := (1 - v) ^ (-(1 / 2 : ℝ))

/-- The straight-segment correction with its integrable endpoint factor extracted. -/
def continuedCorrection (b : ℝ) (w : ℂ) : ℂ :=
  ((b : ℂ) - w) * (((b : ℂ) - w) ^ (-(1 / 2 : ℂ))) / (Real.pi : ℂ) *
    ∫ v in (0 : ℝ)..1, correctionRegular b w v * (correctionWeight v : ℂ)

theorem lower_square_mem_ellipticDomain {q : ℂ} (hq : q.im < 0) : q ^ 2 ∈ ellipticDomain := by
  by_cases hre : q.re = 0
  · right
    simp only [pow_two, Complex.mul_re, hre, zero_mul, zero_sub]
    nlinarith [sq_nonneg q.im]
  · left
    simp only [pow_two, Complex.mul_im]
    intro he
    apply mul_ne_zero hre hq.ne
    nlinarith

theorem correctionParameter_mem_domain {b v : ℝ} {w : ℂ} (hw : w.im < 0)
    (hv : v ∈ Icc 0 1) : correctionParameter b w v ∈ ellipticDomain := by
  rcases hv.1.eq_or_lt with he | hv0
  · have : v = 0 := he.symm
    subst v
    norm_num [correctionParameter, ellipticDomain]
  · apply lower_square_mem_ellipticDomain
    have hh : (((w - b) * (v : ℂ) / 4) : ℂ).im = w.im * v / 4 := by simp
    rw [hh]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hw hv0) (by norm_num)

theorem correctionBase_mem_slitPlane {b v : ℝ} (hb : 0 < b) {w : ℂ} (hw : w.im < 0)
    (hv : v ∈ Icc 0 1) : correctionBase b w v ∈ Complex.slitPlane := by
  rcases hv.2.lt_or_eq with hv1 | rfl
  · apply Complex.mem_slitPlane_iff.mpr
    right
    have hh : (correctionBase b w v).im = w.im * (1 - v) := by
      simp [correctionBase]
    rw [hh]
    exact (mul_neg_of_neg_of_pos hw (by linarith)).ne
  · apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [correctionBase] using (mul_pos hb (by norm_num : (0 : ℝ) < 2))

def correctionDomain (b : ℝ) : Set ℂ :=
  {w | w.im < 0 ∨ (-b < w.re ∧ w.re < b ∧ ‖w - b‖ < 4)}

theorem correctionDomain_isOpen (b : ℝ) : IsOpen (correctionDomain b) := by
  exact (isOpen_lt Complex.continuous_im continuous_const).union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (show Continuous (fun w : ℂ => ‖w - (b : ℂ)‖) by fun_prop) continuous_const)))

theorem correctionParameter_mem_domain_central {b v : ℝ} {w : ℂ}
    (hw : ‖w - b‖ < 4) (hv : v ∈ Icc 0 1) :
    correctionParameter b w v ∈ ellipticDomain := by
  have hq : ‖(w - b) * (v : ℂ) / 4‖ < 1 := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1]
    norm_num
    have hh := mul_le_of_le_one_right (norm_nonneg (w - b)) hv.2
    linarith
  right
  have hn := Complex.abs_re_le_norm (correctionParameter b w v)
  have hnorm : ‖correctionParameter b w v‖ < 1 := by
    unfold correctionParameter
    rw [norm_pow]
    nlinarith [norm_nonneg ((w - b) * (v : ℂ) / 4)]
  exact (le_abs_self _).trans_lt (hn.trans_lt hnorm)

theorem correctionBase_mem_slitPlane_central {b v : ℝ} (hb : 0 < b) {w : ℂ}
    (hw : -b < w.re) (hv : v ∈ Icc 0 1) : correctionBase b w v ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have he : (correctionBase b w v).re = (b + w.re) * (1 - v) + 2 * b * v := by
    simp only [correctionBase, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [he]
  rcases hv.2.lt_or_eq with hv1 | rfl
  · have hfirst : 0 < (b + w.re) * (1 - v) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg hb.le hv.1]
  · nlinarith

theorem correctionParameter_mem_domain_of_mem {b v : ℝ} {w : ℂ}
    (hw : w ∈ correctionDomain b) (hv : v ∈ Icc 0 1) :
    correctionParameter b w v ∈ ellipticDomain := by
  rcases hw with hw | hw
  · exact correctionParameter_mem_domain hw hv
  · exact correctionParameter_mem_domain_central hw.2.2 hv

theorem correctionBase_mem_slitPlane_of_mem {b v : ℝ} (hb : 0 < b) {w : ℂ}
    (hw : w ∈ correctionDomain b) (hv : v ∈ Icc 0 1) :
    correctionBase b w v ∈ Complex.slitPlane := by
  rcases hw with hw | hw
  · exact correctionBase_mem_slitPlane hb hw hv
  · exact correctionBase_mem_slitPlane_central hb hw.1 hv

theorem correctionPrefactor_mem_slitPlane {b : ℝ} {w : ℂ}
    (hw : w ∈ correctionDomain b) : (b : ℂ) - w ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  rcases hw with hw | hw
  · right
    simpa using hw.ne
  · left
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [hw.2.1]

theorem correctionRegular_continuousOn {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun p : ℂ × ℝ => correctionRegular b p.1 p.2)
      (correctionDomain b ×ˢ Icc 0 1) := by
  unfold correctionRegular
  apply ContinuousOn.mul
  · apply complexEllipticK_continuousOn.comp
    · unfold correctionParameter
      fun_prop
    · intro p hp
      exact correctionParameter_mem_domain_of_mem hp.1 hp.2
  · apply ContinuousOn.cpow_const
    · unfold correctionBase
      fun_prop
    · intro p hp
      exact correctionBase_mem_slitPlane_of_mem hb hp.1 hp.2

theorem correctionRegular_continuousOn_interval {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ correctionDomain b) :
    ContinuousOn (correctionRegular b w) (Icc 0 1) :=
  (correctionRegular_continuousOn hb).comp (f := fun v : ℝ => (w, v))
    (by fun_prop) (fun v hv => ⟨hw, hv⟩)

theorem correctionWeight_integrable : IntervalIntegrable correctionWeight volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).comp_sub_left 1
  change IntervalIntegrable (fun v : ℝ => (1 - v) ^ (-(1 / 2 : ℝ))) volume 0 1
  simpa only [sub_zero, sub_self] using h.symm

theorem correctionRegular_weight_integrable {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : w ∈ correctionDomain b) :
    IntervalIntegrable (fun v => correctionRegular b w v * (correctionWeight v : ℂ)) volume 0 1 := by
  have hi : IntervalIntegrable (fun v => (correctionWeight v : ℂ)) volume 0 1 :=
    ⟨correctionWeight_integrable.1.ofReal, correctionWeight_integrable.2.ofReal⟩
  apply IntervalIntegrable.continuousOn_mul hi
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact correctionRegular_continuousOn_interval hb hw

end AperyMoments
