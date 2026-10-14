import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Positivity

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

abbrev Circle := AddCircle (1 : ℝ)
noncomputable def circleMeasure : Measure Circle := haarAddCircle

noncomputable def polynomial (A : Finset ℤ) (s : ℤ → ℝ) : C(Circle, ℂ) :=
  ∑ a ∈ A, (s a : ℂ) • fourier a

theorem polynomial_apply (A : Finset ℤ) (s : ℤ → ℝ) (x : Circle) :
    polynomial A s x = ∑ a ∈ A, (s a : ℂ) * fourier a x := by
  simp [polynomial]

theorem polynomial_fourierCoeff (A : Finset ℤ) (s : ℤ → ℝ) (m : ℤ) :
    fourierCoeff (polynomial A s) m = if m ∈ A then (s m : ℂ) else 0 := by
  classical
  unfold polynomial
  rw [show (⇑(∑ a ∈ A, (s a : ℂ) • fourier a) : Circle → ℂ) =
      ∑ a ∈ A, (fun x : Circle => (s a : ℂ) * fourier a x) by ext; simp]
  rw [fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier]
    simp [Pi.single_apply]
  · intro a ha
    exact ((fourier a).continuous.const_mul (s a : ℂ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem polynomial_integral (A : Finset ℤ) (s : ℤ → ℝ) (h0 : 0 ∉ A) :
    ∫ x, polynomial A s x ∂haarAddCircle = 0 := by
  have h := polynomial_fourierCoeff A s 0
  simpa [fourierCoeff, h0] using h

theorem polynomial_conj (A : Finset ℤ) (s : ℤ → ℝ)
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (x : Circle) :
    conj (polynomial A s x) = polynomial A s x := by
  classical
  simp only [polynomial_apply, map_sum, map_mul, Complex.conj_ofReal, ← fourier_neg]
  apply Finset.sum_bij (fun a _ => -a)
  · intro a ha; exact (hA a).2 ha
  · intro a ha b hb hab; omega
  · intro b hb; exact ⟨-b, (hA b).2 hb, by simp⟩
  · intro a ha; rw [hs a ha]

theorem polynomial_im (A : Finset ℤ) (s : ℤ → ℝ)
    (hA : ∀ a, -a ∈ A ↔ a ∈ A) (hs : ∀ a ∈ A, s (-a) = s a) (x : Circle) :
    (polynomial A s x).im = 0 := by
  have h := congrArg Complex.im (polynomial_conj A s hA hs x)
  simp only [Complex.conj_im] at h
  linarith

/-- A finite complex Fourier polynomial; used for the translated auxiliary functions. -/
noncomputable def complexPolynomial (A : Finset ℤ) (c : ℤ → ℂ) : C(Circle, ℂ) :=
  ∑ a ∈ A, c a • fourier a

theorem complexPolynomial_apply (A : Finset ℤ) (c : ℤ → ℂ) (x : Circle) :
    complexPolynomial A c x = ∑ a ∈ A, c a * fourier a x := by
  simp [complexPolynomial]

theorem complexPolynomial_fourierCoeff (A : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    fourierCoeff (complexPolynomial A c) m = if m ∈ A then c m else 0 := by
  classical
  unfold complexPolynomial
  rw [show (⇑(∑ a ∈ A, c a • fourier a) : Circle → ℂ) =
      ∑ a ∈ A, (fun x : Circle => c a * fourier a x) by ext; simp]
  rw [fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier]
    simp [Pi.single_apply]
  · intro a ha
    exact ((fourier a).continuous.const_mul (c a)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end ChowlaCosine
