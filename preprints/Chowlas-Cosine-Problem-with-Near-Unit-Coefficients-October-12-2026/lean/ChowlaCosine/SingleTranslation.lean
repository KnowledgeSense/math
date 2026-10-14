import ChowlaCosine.ConvolutionFourier
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

set_option maxHeartbeats 1000000

theorem fourier_neg_input (m : ℤ) (x : Circle) :
    fourier m (-x) = conj (fourier m x) := by
  simp only [fourier_apply, zsmul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

theorem fourierCoeff_even_real (h : Circle → ℝ) (heven : ∀ x, h (-x) = h x) (m : ℤ) :
    (fourierCoeff (fun x => (h x : ℂ)) m).im = 0 := by
  have hn := integral_neg_eq_self
    (fun x : Circle => fourier (-m) x * (h x : ℂ)) haarAddCircle
  simp only [fourier_neg_input, heven] at hn
  have heq : conj (fourierCoeff (fun x => (h x : ℂ)) m) =
      fourierCoeff (fun x => (h x : ℂ)) m := by
    unfold fourierCoeff
    simp only [smul_eq_mul]
    rw [← integral_conj]
    simpa only [map_mul, Complex.conj_ofReal] using hn
  have hi := congrArg Complex.im heq
  simp only [Complex.conj_im] at hi
  linarith

theorem finite_bessel (f : C(Circle, ℂ)) (S : Finset ℤ) :
    ∑ m ∈ S, ‖fourierCoeff f m‖^2 ≤ ∫ x, ‖f x‖^2 ∂haarAddCircle := by
  have hs := hasSum_sq_fourierCoeff (ContinuousMap.toLp (E:=ℂ) 2 haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp] at hs
  have he : (∫ x, ‖ContinuousMap.toLp (E:=ℂ) 2 haarAddCircle ℂ f x‖^2 ∂haarAddCircle) =
      ∫ x, ‖f x‖^2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toAEEqFun haarAddCircle f] with x hx
    exact congrArg (fun z : ℂ => ‖z‖^2) hx
  rw [he] at hs
  exact sum_le_hasSum S (fun m _ => sq_nonneg _) hs


noncomputable def complexify (h : C(Circle, ℝ)) : C(Circle, ℂ) :=
  ⟨fun x => (h x : ℂ), Complex.continuous_ofReal.comp h.continuous⟩

theorem even_coefficient_square (h : C(Circle, ℝ)) (heven : ∀ x, h (-x) = h x) (m : ℤ) :
    (fourierCoeff (complexify h) m * fourierCoeff (complexify h) m).re =
      ‖fourierCoeff (complexify h) m‖^2 := by
  have hi := fourierCoeff_even_real h heven m
  change (fourierCoeff (complexify h) m).im = 0 at hi
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, hi]
  ring

theorem finite_even_pairing_bound (h : C(Circle, ℝ)) (heven : ∀ x, h (-x) = h x)
    (S : Finset ℤ) (v : ℤ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hv : ∀ m ∈ S, v m ≤ c) :
    (∑ m ∈ S, v m * (fourierCoeff (complexify h) m * fourierCoeff (complexify h) m).re) ≤
      c * ∫ x, (h x)^2 ∂haarAddCircle := by
  have hb := finite_bessel (complexify h) S
  have he : (∫ x, ‖complexify h x‖^2 ∂haarAddCircle) =
      ∫ x, (h x)^2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [complexify, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [he] at hb
  calc
    _ = ∑ m ∈ S, v m * ‖fourierCoeff (complexify h) m‖^2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [even_coefficient_square h heven]
    _ ≤ ∑ m ∈ S, c * ‖fourierCoeff (complexify h) m‖^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_right (hv m hm) (sq_nonneg _)
    _ = c * ∑ m ∈ S, ‖fourierCoeff (complexify h) m‖^2 := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hc


theorem convolution_pairing_upper (h : C(Circle, ℝ)) (heven : ∀ x, h (-x) = h x)
    (S : Finset ℤ) (v : ℤ → ℝ) (c : ℝ) (hc : 0 ≤ c) (hv : ∀ m ∈ S, v m ≤ c) :
    (∫ x, convolve (complexify h) (complexify h) x * conj (polynomial S v x)
      ∂haarAddCircle).re ≤ c * ∫ x, (h x)^2 ∂haarAddCircle := by
  have hi : Integrable (complexify h) haarAddCircle :=
    (complexify h).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp := integral_mul_conj_polynomial (integrable_convolve hi hi) S v
  simp_rw [fourierCoeff_convolve (complexify h).continuous (complexify h).continuous] at hp
  have hr := congrArg Complex.re hp
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  rw [hr]
  exact finite_even_pairing_bound h heven S v c hc hv


theorem integral_convolve_of_continuous {f g : Circle → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ x, convolve f g x ∂haarAddCircle) =
      (∫ x, f x ∂haarAddCircle) * (∫ x, g x ∂haarAddCircle) := by
  have h := fourierCoeff_convolve hf hg 0
  simpa [fourierCoeff] using h

theorem convolution_pairing_with_constant (h : C(Circle, ℝ))
    (heven : ∀ x, h (-x) = h x) (S : Finset ℤ) (v : ℤ → ℝ)
    (c M : ℝ) (hc : 0 ≤ c) (hv : ∀ m ∈ S, v m ≤ c) :
    (∫ x, convolve (complexify h) (complexify h) x * (conj (polynomial S v x) + (M:ℂ))
      ∂haarAddCircle).re ≤ c * (∫ x, (h x)^2 ∂haarAddCircle) + M * (∫ x, h x ∂haarAddCircle)^2 := by
  have hi : Integrable (complexify h) haarAddCircle :=
    (complexify h).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconv := integrable_convolve hi hi
  have hprod : Integrable (fun x => convolve (complexify h) (complexify h) x *
      conj (polynomial S v x)) haarAddCircle := by
    apply hconv.mul_bdd (Complex.continuous_conj.comp (polynomial S v).continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa using (polynomial S v).norm_coe_le_norm x)
  have hmean : (∫ x, complexify h x ∂haarAddCircle) = ((∫ x, h x ∂haarAddCircle : ℝ):ℂ) := by
    exact integral_complex_ofReal
  simp_rw [mul_add]
  rw [integral_add hprod (hconv.mul_const _), integral_mul_const,
    integral_convolve_of_continuous (complexify h).continuous (complexify h).continuous, hmean]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  have hb := convolution_pairing_upper h heven S v c hc hv
  nlinarith

end ChowlaCosine
