import ChowlaCosine.BedertPointwise
import ChowlaCosine.ConvolutionFourier
import ChowlaCosine.WeightedRoth
import ChowlaCosine.LocalFourier

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

private theorem fc_add {f g : Circle → ℂ} (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) (m : ℤ) :
    fourierCoeff (fun x => f x + g x) m = fourierCoeff f m + fourierCoeff g m := by
  exact congrFun (fourierCoeff.add hf hg) m

private theorem integrable_continuous {f : Circle → ℂ} (hf : Continuous f) :
    Integrable f haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem auxiliaryF_complex (F : Circle → ℝ) (t : ℤ) (x : Circle) :
    (auxiliaryF F t x : ℂ) =
      2 * (F x : ℂ) + (-Complex.I) * ((F x : ℂ) * fourier t x) +
        Complex.I * ((F x : ℂ) * fourier (-t) x) := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [auxiliaryF, sineWave, Complex.mul_re, Complex.mul_im]
  ring

theorem fourierCoeff_auxiliaryF {F : Circle → ℝ} (hF : Continuous F) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryF F t x : ℂ)) m =
      2 * fourierCoeff (fun x => (F x : ℂ)) m -
        Complex.I * fourierCoeff (fun x => (F x : ℂ)) (m-t) +
        Complex.I * fourierCoeff (fun x => (F x : ℂ)) (m+t) := by
  have hf : Continuous (fun x => (F x : ℂ)) := Complex.continuous_ofReal.comp hF
  have hi := integrable_continuous hf
  have ht : Integrable (fun x => (F x : ℂ) * fourier t x) haarAddCircle :=
    integrable_continuous (hf.mul (fourier t).continuous)
  have hnt : Integrable (fun x => (F x : ℂ) * fourier (-t) x) haarAddCircle :=
    integrable_continuous (hf.mul (fourier (-t)).continuous)
  simp_rw [auxiliaryF_complex]
  have hi2 : Integrable (fun x => 2 * (F x : ℂ) + (-Complex.I)*((F x : ℂ)*fourier t x)) haarAddCircle :=
    (hi.const_mul 2).add (ht.const_mul (-Complex.I))
  rw [fc_add hi2
      (hnt.const_mul Complex.I), fc_add (hi.const_mul 2) (ht.const_mul (-Complex.I))]
  simp only [fourierCoeff.const_mul, fourierCoeff_mul_character, sub_neg_eq_add]
  ring

theorem complex_realConvolve (f g : Circle → ℝ) (x : Circle) :
    (realConvolve f g x : ℂ) = convolve (fun y => (f y : ℂ)) (fun y => (g y : ℂ)) x := by
  unfold realConvolve convolve
  rw [← integral_complex_ofReal]
  simp only [Complex.ofReal_mul]

theorem phaseCosine_complex (t : ℤ) (x : Circle) :
    (phaseCosine t x : ℂ) = omega * fourier t x + conj omega * fourier (-t) x := by
  unfold phaseCosine
  rw [phase_eq_two_omega, fourier_neg]
  apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;> ring

theorem auxiliaryR_complex (F : Circle → ℝ) (t : ℤ) (x : Circle) :
    (auxiliaryR F t x : ℂ) =
      (realConvolve (auxiliaryF F t) (auxiliaryF F t) x : ℂ) +
      (-omega) * ((realConvolve (auxiliaryF F t) (auxiliaryF F t) x : ℂ) * fourier t x) +
      (-conj omega) * ((realConvolve (auxiliaryF F t) (auxiliaryF F t) x : ℂ) * fourier (-t) x) := by
  unfold auxiliaryR
  push_cast
  rw [phaseCosine_complex]
  ring

theorem continuous_auxiliaryF {F : Circle → ℝ} (hF : Continuous F) (t : ℤ) :
    Continuous (auxiliaryF F t) := by
  unfold auxiliaryF sineWave
  exact (continuous_const.mul
    (continuous_const.add (Complex.continuous_im.comp (fourier t).continuous))).mul hF

theorem fourierCoeff_auxiliaryR {F : Circle → ℝ} (hF : Continuous F) (t m : ℤ) :
    fourierCoeff (fun x => (auxiliaryR F t x : ℂ)) m =
      (fourierCoeff (fun x => (auxiliaryF F t x : ℂ)) m)^2 -
      omega * (fourierCoeff (fun x => (auxiliaryF F t x : ℂ)) (m-t))^2 -
      conj omega * (fourierCoeff (fun x => (auxiliaryF F t x : ℂ)) (m+t))^2 := by
  let H : Circle → ℂ := fun x => (realConvolve (auxiliaryF F t) (auxiliaryF F t) x : ℂ)
  have hf : Continuous (fun x => (auxiliaryF F t x : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_auxiliaryF hF t)
  have hh : Continuous H := by
    simp only [H, complex_realConvolve]
    exact (HasCompactSupport.of_compactSpace _).continuous_convolution_right
      (ContinuousLinearMap.mul ℂ ℂ) hf.locallyIntegrable hf
  have hc (k : ℤ) : fourierCoeff H k =
      (fourierCoeff (fun x => (auxiliaryF F t x : ℂ)) k)^2 := by
    simp only [H, complex_realConvolve]
    rw [fourierCoeff_convolve hf hf, pow_two]
  have hi := integrable_continuous hh
  have ht : Integrable (fun x => H x * fourier t x) haarAddCircle :=
    integrable_continuous (hh.mul (fourier t).continuous)
  have hnt : Integrable (fun x => H x * fourier (-t) x) haarAddCircle :=
    integrable_continuous (hh.mul (fourier (-t)).continuous)
  have hi2 : Integrable (fun x => H x + (-omega)*(H x * fourier t x)) haarAddCircle :=
    hi.add (ht.const_mul (-omega))
  simp_rw [auxiliaryR_complex]
  change fourierCoeff (fun x => H x + (-omega)*(H x * fourier t x) +
    (-conj omega)*(H x * fourier (-t) x)) m = _
  rw [fc_add hi2 (hnt.const_mul (-conj omega)), fc_add hi (ht.const_mul (-omega))]
  simp only [fourierCoeff.const_mul, fourierCoeff_mul_character, sub_neg_eq_add, hc]
  ring

theorem fourierCoeff_real_reflect (r : Circle → ℝ) (m : ℤ) :
    fourierCoeff (fun x => (r (-x) : ℂ)) m = conj (fourierCoeff (fun x => (r x : ℂ)) m) := by
  have h := integral_neg_eq_self
    (fun x : Circle => fourier (-m) x * (r (-x) : ℂ)) haarAddCircle
  have hn (x : Circle) : fourier (-m) (-x) = conj (fourier (-m) x) := by
    simp only [fourier_apply, zsmul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  simp only [neg_neg, hn] at h
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [← h, ← integral_conj]
  congr 1
  ext x
  simp

theorem fourierCoeff_evenPart {r : Circle → ℝ} (hr : Continuous r) (m : ℤ) :
    fourierCoeff (fun x => (((r x + r (-x))/2 : ℝ) : ℂ)) m =
      ((fourierCoeff (fun x => (r x : ℂ)) m).re : ℂ) := by
  have hi : Integrable (fun x => (r x : ℂ)) haarAddCircle :=
    integrable_continuous (Complex.continuous_ofReal.comp hr)
  have hn : Integrable (fun x => (r (-x) : ℂ)) haarAddCircle :=
    integrable_continuous (Complex.continuous_ofReal.comp (hr.comp continuous_neg))
  have he : (fun x : Circle => (((r x + r (-x))/2 : ℝ) : ℂ)) =
      (fun x => (1/2 : ℂ) * ((r x : ℂ) + (r (-x) : ℂ))) := by
    ext x; push_cast; ring
  change fourierCoeff (fun x => (((r x + r (-x))/2 : ℝ) : ℂ)) m = _
  rw [he, fourierCoeff.const_mul, fc_add hi hn, fourierCoeff_real_reflect, Complex.add_conj]
  push_cast
  ring

theorem fourierCoeff_oddPart {r : Circle → ℝ} (hr : Continuous r) (m : ℤ) :
    fourierCoeff (fun x => (((r x - r (-x))/2 : ℝ) : ℂ)) m =
      Complex.I * ((fourierCoeff (fun x => (r x : ℂ)) m).im : ℂ) := by
  have hi : Integrable (fun x => (r x : ℂ)) haarAddCircle :=
    integrable_continuous (Complex.continuous_ofReal.comp hr)
  have hn : Integrable (fun x => (r (-x) : ℂ)) haarAddCircle :=
    integrable_continuous (Complex.continuous_ofReal.comp (hr.comp continuous_neg))
  have he : (fun x : Circle => (((r x - r (-x))/2 : ℝ) : ℂ)) =
      (fun x => (1/2 : ℂ) * ((r x : ℂ) + (-1 : ℂ) * (r (-x) : ℂ))) := by
    ext x; push_cast; ring
  rw [he, fourierCoeff.const_mul, fc_add hi (hn.const_mul (-1)), fourierCoeff.const_mul,
    fourierCoeff_real_reflect]
  have hh := Complex.sub_conj (fourierCoeff (fun x => (r x : ℂ)) m)
  calc
    _ = (1/2:ℂ) * (fourierCoeff (fun x => (r x : ℂ)) m -
      conj (fourierCoeff (fun x => (r x : ℂ)) m)) := by ring
    _ = _ := by rw [hh]; push_cast; ring

end ChowlaCosine
