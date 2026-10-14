import ChowlaCosine.PaperAuxiliary
import ChowlaCosine.AnalyticComparison
import ChowlaCosine.SingleTranslation

namespace ChowlaCosine
open MeasureTheory AddCircle
open scoped ComplexConjugate

theorem paper_pairing_upper {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ}
    (t : ℤ) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hK : 0 ≤ K) (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    ‖∫ x, (auxiliaryPhi (realPolynomial A s) t x : ℂ) *
      conj (convolve (selector A s t) (selector A s t) x) ∂haarAddCircle‖ ≤
      (4.86 : ℝ) * (∫ x, ‖selector A s t x‖^2 ∂haarAddCircle) +
      32*K^2 * (∫ x, ‖selector A s t x‖ ∂haarAddCircle)^2 := by
  let g : C(Circle, ℂ) := ⟨selector A s t, continuous_selector A s t⟩
  let h : C(Circle, ℝ) := ⟨fun x => ‖g x‖, g.continuous.norm⟩
  have hr := continuous_auxiliaryR (continuous_realPolynomial A s) t
  let φ : C(Circle, ℝ) := ⟨auxiliaryPhi (realPolynomial A s) t,
    (hr.sub (hr.comp continuous_neg)).div_const 2⟩
  let ψ : C(Circle, ℝ) := ⟨auxiliaryPsi (realPolynomial A s) t,
    (hr.add (hr.comp continuous_neg)).div_const 2⟩
  have hmean : ∫ x, realPolynomial A s x ∂haarAddCircle = 0 := by
    have he : ((∫ x, realPolynomial A s x ∂haarAddCircle : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      simp_rw [complex_realPolynomial hA hs]
      exact polynomial_integral A s h0
    exact_mod_cast he
  have heven : ∀ x, realPolynomial A s (-x) = realPolynomial A s x := by
    intro x
    simp only [realPolynomial, polynomial_neg_argument, Complex.conj_re]
  have hb := convolution_pairing_comparison g φ ψ (32*K^2)
    (bedert_pointwise (continuous_realPolynomial A s) hmean heven hK hlower t)
  have hu := convolution_pairing_with_constant h
    (fun x => norm_selector_neg A s t x) (auxiliarySpectrum A t)
    (fun m => R (localVector A s t m)) (4.86 : ℝ) (32*K^2)
    (by norm_num) (fun m _ => by have hh := R_le _ (admissible_localVector hcoeff t m); norm_num at hh ⊢; exact hh)
  have hpoly := auxiliaryPsi_eq_polynomial hA hs t
  have heq : (∫ x, convolve (complexify h) (complexify h) x *
      (conj (polynomial (auxiliarySpectrum A t) (fun m => R (localVector A s t m)) x) +
        ((32*K^2 : ℝ):ℂ)) ∂haarAddCircle).re =
      ∫ x, (ψ x + 32*K^2) * realConvolve h h x ∂haarAddCircle := by
    rw [← hpoly]
    have hp : (fun x => convolve (complexify h) (complexify h) x *
        (conj ((auxiliaryPsi (realPolynomial A s) t x : ℝ):ℂ) + ((32*K^2:ℝ):ℂ))) =
        fun x => (((ψ x + 32*K^2) * realConvolve h h x : ℝ):ℂ) := by
      funext x
      rw [show convolve (complexify h) (complexify h) x = (realConvolve h h x : ℂ) from
        (complex_realConvolve h h x).symm]
      simp only [Complex.conj_ofReal, Complex.ofReal_mul, Complex.ofReal_add]
      change _ = ((auxiliaryPsi (realPolynomial A s) t x : ℂ) + _) * _
      ring
    rw [hp, integral_complex_ofReal]
    rfl
  rw [heq] at hu
  exact hb.trans hu

end ChowlaCosine
