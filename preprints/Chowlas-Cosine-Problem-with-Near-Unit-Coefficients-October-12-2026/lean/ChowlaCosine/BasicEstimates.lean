import ChowlaCosine.FourierPolynomial

namespace ChowlaCosine
open MeasureTheory AddCircle

/-- Every Fourier coefficient is bounded by the integral of the absolute value. -/
theorem norm_fourierCoeff_le (f : Circle → ℂ) (m : ℤ) :
    ‖fourierCoeff f m‖ ≤ ∫ x, ‖f x‖ ∂haarAddCircle := by
  calc
    ‖fourierCoeff f m‖ ≤ ∫ x, ‖fourier (-m) x • f x‖ ∂haarAddCircle :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

/-- The mean-zero estimate used in Lemma 2.1, on the original circle measure. -/
theorem integral_abs_le_twice {f : Circle → ℝ} {K : ℝ}
    (hf : Integrable f haarAddCircle) (hmean : ∫ x, f x ∂haarAddCircle = 0)
    (hlower : ∀ x, -K ≤ f x) :
    ∫ x, |f x| ∂haarAddCircle ≤ 2 * K := by
  have hK : 0 ≤ K := by
    have hi := integral_mono (integrable_const (-K)) hf hlower
    simpa [hmean] using hi
  have hbound : ∀ x, |f x| ≤ f x + 2 * K := by
    intro x
    apply abs_le.mpr
    constructor <;> linarith [hlower x]
  calc
    ∫ x, |f x| ∂haarAddCircle ≤ ∫ x, (f x + 2 * K) ∂haarAddCircle :=
      integral_mono hf.abs (hf.add (integrable_const _)) hbound
    _ = 2 * K := by rw [integral_add hf (integrable_const _), hmean]; simp

theorem fourierCoeff_const (c : ℂ) (m : ℤ) :
    fourierCoeff (fun _ : Circle => c) m = if m = 0 then c else 0 := by
  have h := fourierCoeff.const_mul (T := (1 : ℝ)) (fourier 0) c m
  simpa [fourierCoeff_fourier, Pi.single_apply] using h

theorem polynomial_coefficient_le {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re)
    {a : ℤ} (ha : a ∈ A) : |s a| ≤ K := by
  have ha0 : a ≠ 0 := by intro h; exact h0 (h ▸ ha)
  have hi : Integrable (polynomial A s) haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcoeff : fourierCoeff (fun x => polynomial A s x + (K : ℂ)) a = (s a : ℂ) := by
    have hh := congrFun (fourierCoeff.add hi (integrable_const (K : ℂ))) a
    change fourierCoeff (fun x : Circle => polynomial A s x + (K : ℂ)) a =
      fourierCoeff (polynomial A s) a + fourierCoeff (fun _ : Circle => (K : ℂ)) a at hh
    simpa only [polynomial_fourierCoeff, fourierCoeff_const, ite_eq_left ha, ite_eq_right ha0, add_zero] using hh
  have hnorm : ∀ x : Circle, ‖polynomial A s x + (K : ℂ)‖ = (polynomial A s x).re + K := by
    intro x
    have he : polynomial A s x + (K : ℂ) = ((polynomial A s x).re + K : ℝ) := by
      apply Complex.ext <;> simp [polynomial_im A s hA hs x]
    rw [he, Complex.norm_of_nonneg (by linarith [hlower x])]
  have hb := norm_fourierCoeff_le (fun x => polynomial A s x + (K : ℂ)) a
  rw [hcoeff] at hb
  simp only [hnorm] at hb
  change ‖(s a : ℂ)‖ ≤ ∫ x, RCLike.re (polynomial A s x) + K ∂haarAddCircle at hb
  rw [integral_add hi.re (integrable_const K), integral_re hi, polynomial_integral A s h0] at hb
  simpa [Complex.norm_real, Real.norm_eq_abs] using hb

theorem polynomial_integral_norm_le {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    ∫ x, ‖polynomial A s x‖ ∂haarAddCircle ≤ 2 * K := by
  have hi : Integrable (polynomial A s) haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmean : ∫ x, (polynomial A s x).re ∂haarAddCircle = 0 := by
    change ∫ x, RCLike.re (polynomial A s x) ∂haarAddCircle = 0
    rw [integral_re hi, polynomial_integral A s h0]; rfl
  have hnorm : ∀ x : Circle, ‖polynomial A s x‖ = |(polynomial A s x).re| := by
    intro x
    have he : polynomial A s x = ((polynomial A s x).re : ℂ) := by
      apply Complex.ext <;> simp [polynomial_im A s hA hs x]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    simp
  simp only [hnorm]
  change ∫ x, |RCLike.re (polynomial A s x)| ∂haarAddCircle ≤ 2 * K
  exact integral_abs_le_twice hi.re hmean hlower

end ChowlaCosine
