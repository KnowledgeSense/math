import ChowlaCosine.FourierPolynomial

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

/-- Finite Parseval pairing, without any Fourier-series convergence hypothesis. -/
theorem integral_mul_conj_polynomial {f : Circle → ℂ}
    (hf : Integrable f haarAddCircle) (A : Finset ℤ) (s : ℤ → ℝ) :
    ∫ x, f x * conj (polynomial A s x) ∂haarAddCircle =
      ∑ a ∈ A, (s a : ℂ) * fourierCoeff f a := by
  classical
  simp only [polynomial_apply, map_sum, map_mul, Complex.conj_ofReal, ← fourier_neg,
    Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [show (fun x : Circle => f x * ((s a : ℂ) * fourier (-a) x)) =
      (fun x : Circle => (s a : ℂ) * (fourier (-a) x • f x)) by ext; simp; ring]
    exact integral_const_mul _ _
  · intro a ha
    convert (hf.fourier_smul (-a)).const_mul (s a : ℂ) using 1
    ext x
    simp only [smul_eq_mul]
    ring

/-- Parseval for a finite Fourier polynomial. -/
theorem integral_norm_sq_polynomial (A : Finset ℤ) (s : ℤ → ℝ) :
    ∫ x, ‖polynomial A s x‖ ^ 2 ∂haarAddCircle = ∑ a ∈ A, (s a) ^ 2 := by
  have hi : Integrable (polynomial A s) haarAddCircle :=
    (polynomial A s).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := integral_mul_conj_polynomial hi A s
  simp only [polynomial_fourierCoeff] at h
  have hs : (∑ a ∈ A, (s a : ℂ) * if a ∈ A then (s a : ℂ) else 0) =
      ((∑ a ∈ A, (s a) ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro a ha
    simp [ha, pow_two]
  rw [hs] at h
  have hn : (fun x : Circle => polynomial A s x * conj (polynomial A s x)) =
      (fun x : Circle => ((‖polynomial A s x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    simpa only [Complex.ofReal_pow] using Complex.mul_conj' (polynomial A s x)
  rw [hn, integral_complex_ofReal] at h
  exact_mod_cast h

end ChowlaCosine
