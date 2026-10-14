import ChowlaCosine.Convolution

namespace ChowlaCosine
open MeasureTheory AddCircle
set_option maxHeartbeats 1000000

theorem fourier_add_argument (n : ℤ) (x y : Circle) :
    fourier n (x+y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourierCoeff_translate (g : Circle → ℂ) (m : ℤ) (y : Circle) :
    ∫ x, fourier (-m) x * g (x-y) ∂haarAddCircle = fourier (-m) y * fourierCoeff g m := by
  have h := integral_add_right_eq_self (μ := (haarAddCircle : Measure Circle)) (fun x : Circle => fourier (-m) x * g (x-y)) y
  simp only [add_sub_cancel_right, fourier_add_argument] at h
  rw [show (fun x : Circle => (fourier (-m) x * fourier (-m) y) * g x) =
    (fun x => fourier (-m) y * (fourier (-m) x * g x)) by ext; ring,
    integral_const_mul] at h
  exact h.symm

/-- Fourier multiplication for convolution on the original Haar circle. -/
theorem fourierCoeff_convolve {f g : Circle → ℂ}
    (hf : Continuous f) (hg : Continuous g) (m : ℤ) :
    fourierCoeff (convolve f g) m = fourierCoeff f m * fourierCoeff g m := by
  have hc : Continuous (fun p : Circle × Circle =>
      fourier (-m) p.1 * (f p.2 * g (p.1-p.2))) := by
    exact ((fourier (-m)).continuous.comp continuous_fst).mul
      ((hf.comp continuous_snd).mul (hg.comp (continuous_fst.sub continuous_snd)))
  have hi : Integrable (fun p : Circle × Circle =>
      fourier (-m) p.1 * (f p.2 * g (p.1-p.2))) (haarAddCircle.prod haarAddCircle) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold fourierCoeff convolve
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hi]
  have he : ∀ y : Circle,
      (∫ x, fourier (-m) x * (f y * g (x-y)) ∂haarAddCircle) =
      (fourier (-m) y * f y) * fourierCoeff g m := by
    intro y
    rw [show (fun x : Circle => fourier (-m) x * (f y * g (x-y))) =
      (fun x => f y * (fourier (-m) x * g (x-y))) by ext; ring,
      integral_const_mul, fourierCoeff_translate]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  rw [integral_const_mul]
  rfl

end ChowlaCosine
