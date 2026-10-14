import ChowlaCosine.FiniteParseval
import Mathlib.Analysis.Convolution

namespace ChowlaCosine
set_option maxHeartbeats 400000
open MeasureTheory AddCircle
open scoped ComplexConjugate

noncomputable def convolve (f g : Circle → ℂ) (x : Circle) : ℂ :=
  ∫ y, f y * g (x - y) ∂haarAddCircle

theorem fourier_sub_argument (n : ℤ) (x y : Circle) :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  simp only [fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg,
    AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]

theorem convolve_polynomial_right {f : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (A : Finset ℤ) (s : ℤ → ℝ) (x : Circle) :
    convolve f (polynomial A s) x =
      ∑ a ∈ A, (s a : ℂ) * fourier a x * fourierCoeff f a := by
  classical
  unfold convolve
  simp only [polynomial_apply, Finset.mul_sum, fourier_sub_argument]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [show (fun y : Circle => f y * ((s a : ℂ) * (fourier a x * conj (fourier a y)))) =
      (fun y : Circle => ((s a : ℂ) * fourier a x) * (fourier (-a) y • f y)) by
        ext y; rw [fourier_neg]; simp only [smul_eq_mul]; ring]
    exact integral_const_mul _ _
  · intro a ha
    convert (hf.fourier_smul (-a)).const_mul ((s a : ℂ) * fourier a x) using 1
    ext y; rw [fourier_neg]; simp only [smul_eq_mul]; ring

theorem integrable_convolve {f g : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) :
    Integrable (convolve f g) haarAddCircle :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

/-- Young's L¹ inequality for the actual circle convolution. -/
theorem integral_norm_convolve_le {f g : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) :
    ∫ x, ‖convolve f g x‖ ∂haarAddCircle ≤
      (∫ x, ‖f x‖ ∂haarAddCircle) * (∫ x, ‖g x‖ ∂haarAddCircle) := by
  have hn : Integrable
      (fun x : Circle => ∫ y, ‖f y‖ * ‖g (x-y)‖ ∂haarAddCircle) haarAddCircle :=
    by
      have h := hf.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg.norm
      convert h using 1
      funext x
      rfl
  calc
    _ ≤ ∫ x, (∫ y, ‖f y‖ * ‖g (x-y)‖ ∂haarAddCircle) ∂haarAddCircle := by
      apply integral_mono (integrable_convolve hf hg).norm hn
      intro x
      simpa only [convolve, norm_mul] using
        norm_integral_le_integral_norm (fun y : Circle => f y * g (x-y))
    _ = _ := by
      have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm
      simpa only [MeasureTheory.convolution, ContinuousLinearMap.mul_apply'] using h

end ChowlaCosine
