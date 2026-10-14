import ChowlaCosine.BasicEstimates
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace ChowlaCosine
open MeasureTheory AddCircle

noncomputable def realConvolve (f g : Circle → ℝ) (x : Circle) : ℝ :=
  ∫ y, f y * g (x - y) ∂haarAddCircle

/-- The positivity argument underlying Bedert's auxiliary polynomial. -/
theorem realConvolve_self_lower {f : Circle → ℝ} {L : ℝ}
    (hf : Continuous f) (hmean : ∫ y, f y ∂haarAddCircle = 0)
    (hlower : ∀ y, -L ≤ f y) (x : Circle) :
    -L ^ 2 ≤ realConvolve f f x := by
  have hi : Integrable f haarAddCircle := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Continuous (fun y : Circle => f (x - y)) := hf.comp (continuous_const.sub continuous_id)
  have hsi : Integrable (fun y : Circle => f (x-y)) haarAddCircle := hs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpi : Integrable (fun y : Circle => f y * f (x-y)) haarAddCircle := (hf.mul hs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos : 0 ≤ ∫ y, (f y + L) * (f (x - y) + L) ∂haarAddCircle :=
    integral_nonneg (fun y => mul_nonneg (by linarith [hlower y]) (by linarith [hlower (x-y)]))
  have he : (fun y : Circle => (f y + L) * (f (x-y) + L)) =
      (fun y => ((f y * f (x-y) + L * f y) + L * f (x-y)) + L^2) := by
    ext y; ring
  have hi2 : Integrable (fun y => f y * f (x-y) + L * f y) haarAddCircle := hpi.add (hi.const_mul L)
  have hi3 : Integrable (fun y => f y * f (x-y) + L * f y + L * f (x-y)) haarAddCircle := hi2.add (hsi.const_mul L)
  rw [he, integral_add hi3 (integrable_const _),
    integral_add hi2 (hsi.const_mul L),
    integral_add hpi (hi.const_mul L), integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self, hmean] at hpos
  simp at hpos
  unfold realConvolve
  linarith

/-- Even/odd splitting of a real function bounded below. -/
theorem abs_oddPart_le_evenPart {r : Circle → ℝ} {M : ℝ}
    (hr : ∀ x, -M ≤ r x) (x : Circle) :
    |(r x - r (-x)) / 2| ≤ (r x + r (-x)) / 2 + M := by
  apply abs_le.mpr
  constructor <;> linarith [hr x, hr (-x)]

noncomputable def sineWave (t : ℤ) (x : Circle) : ℝ := (fourier t x).im
noncomputable def phaseCosine (t : ℤ) (x : Circle) : ℝ :=
  (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * fourier t x).re
noncomputable def auxiliaryF (F : Circle → ℝ) (t : ℤ) (x : Circle) : ℝ :=
  2 * (1 + sineWave t x) * F x
noncomputable def auxiliaryR (F : Circle → ℝ) (t : ℤ) (x : Circle) : ℝ :=
  (1 - phaseCosine t x) * realConvolve (auxiliaryF F t) (auxiliaryF F t) x
noncomputable def auxiliaryPsi (F : Circle → ℝ) (t : ℤ) (x : Circle) : ℝ :=
  (auxiliaryR F t x + auxiliaryR F t (-x)) / 2
noncomputable def auxiliaryPhi (F : Circle → ℝ) (t : ℤ) (x : Circle) : ℝ :=
  (auxiliaryR F t x - auxiliaryR F t (-x)) / 2

theorem abs_sineWave_le_one (t : ℤ) (x : Circle) : |sineWave t x| ≤ 1 := by
  simpa [sineWave, fourier_apply] using Complex.abs_im_le_norm (fourier t x)

theorem abs_phaseCosine_le_one (t : ℤ) (x : Circle) : |phaseCosine t x| ≤ 1 := by
  have h := Complex.abs_re_le_norm
    (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * fourier t x)
  simpa [phaseCosine, norm_mul, Complex.norm_exp, fourier_apply] using h

theorem sineWave_neg (t : ℤ) (x : Circle) : sineWave t (-x) = -sineWave t x := by
  simp only [sineWave, fourier_apply, zsmul_neg, AddCircle.toCircle_neg,
    Circle.coe_inv_eq_conj, Complex.conj_im]

theorem auxiliaryF_mean_zero {F : Circle → ℝ} (hF : Continuous F)
    (hmean : ∫ x, F x ∂haarAddCircle = 0) (heven : ∀ x, F (-x) = F x) (t : ℤ) :
    ∫ x, auxiliaryF F t x ∂haarAddCircle = 0 := by
  have hi : Integrable F haarAddCircle :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun x => sineWave t x * F x) haarAddCircle :=
    ((Complex.continuous_im.comp (fourier t).continuous).mul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : ∫ x, sineWave t x * F x ∂haarAddCircle = 0 := by
    have hh := integral_neg_eq_self (fun x => sineWave t x * F x) haarAddCircle
    simp only [sineWave_neg, heven, neg_mul, integral_neg] at hh
    linarith
  have he : auxiliaryF F t = fun x => 2 * F x + 2 * (sineWave t x * F x) := by
    ext x; unfold auxiliaryF; ring
  rw [he, integral_add (hi.const_mul 2) (hs.const_mul 2), integral_const_mul,
    integral_const_mul, hmean, hz]
  ring

theorem bedert_pointwise {F : Circle → ℝ} {K : ℝ}
    (hF : Continuous F) (hmean : ∫ x, F x ∂haarAddCircle = 0)
    (heven : ∀ x, F (-x) = F x) (hK : 0 ≤ K) (hlower : ∀ x, -K ≤ F x)
    (t : ℤ) (x : Circle) :
    |auxiliaryPhi F t x| ≤ auxiliaryPsi F t x + 32 * K^2 := by
  have hf : Continuous (auxiliaryF F t) := by
    unfold auxiliaryF sineWave
    exact (continuous_const.mul (continuous_const.add (Complex.continuous_im.comp (fourier t).continuous))).mul hF
  have hfl : ∀ y, -(4*K) ≤ auxiliaryF F t y := by
    intro y
    obtain ⟨hs0, hs1⟩ := abs_le.mp (abs_sineWave_le_one t y)
    have hp := mul_nonneg (show 0 ≤ 2*(1+sineWave t y) by linarith)
      (show 0 ≤ F y + K by linarith [hlower y])
    have hk := mul_nonneg hK (show 0 ≤ 1-sineWave t y by linarith)
    unfold auxiliaryF
    nlinarith
  have hr : ∀ y, -(32*K^2) ≤ auxiliaryR F t y := by
    intro y
    have hc := realConvolve_self_lower hf (auxiliaryF_mean_zero hF hmean heven t) hfl y
    obtain ⟨hp0, hp1⟩ := abs_le.mp (abs_phaseCosine_le_one t y)
    have hprod := mul_nonneg (show 0 ≤ 1-phaseCosine t y by linarith)
      (show 0 ≤ realConvolve (auxiliaryF F t) (auxiliaryF F t) y + (4*K)^2 by linarith)
    have hprod2 := mul_nonneg (sq_nonneg K) (show 0 ≤ 1+phaseCosine t y by linarith)
    unfold auxiliaryR
    nlinarith
  exact abs_oddPart_le_evenPart hr x

end ChowlaCosine
