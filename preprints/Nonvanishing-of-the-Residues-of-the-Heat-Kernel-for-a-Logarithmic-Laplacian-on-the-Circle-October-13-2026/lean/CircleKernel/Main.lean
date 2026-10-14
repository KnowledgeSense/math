import CircleKernel.PoleOrder
import CircleKernel.SpectralCoordinates
import CircleKernel.OperatorConjugate

noncomputable section
open Filter
open scoped Topology ComplexConjugate
namespace CircleKernel

/-- There are no other singularities of the original diagonal spectral kernel. -/
theorem continuedKernel_analyticAt_iff (t : ℂ) :
    AnalyticAt ℂ continuedKernel t ↔ ∀ m : ℕ, t ≠ polePoint m := by
  constructor
  · intro h m hm
    subst t
    exact continuedKernel_not_continuousAt_pole m h.continuousAt
  · intro ht
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · exact (continuedKernel_meromorphic t).eventually_analyticAt.mono fun _ h => h.differentiableAt
    · exact (continuedKernel_differentiableAt t ht).continuousAt

/-- Exact pole set, with the order defined by the genuine meromorphic germ. -/
theorem continuedKernel_poles_iff (t : ℂ) :
    meromorphicOrderAt continuedKernel t < 0 ↔ ∃ m : ℕ, t=polePoint m := by
  constructor
  · intro h
    by_contra hn
    have ha := (continuedKernel_analyticAt_iff t).mpr (by simpa using hn)
    exact not_lt_of_ge ha.meromorphicOrderAt_nonneg h
  · rintro ⟨m,rfl⟩
    rw [continuedKernel_simple_pole]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)

/-- The meromorphic continuation is of the original bilateral Fourier kernel on its diagonal. -/
theorem continuedKernel_bilateral_diagonal (t : ℂ) (ht : 1/2 < t.re) (φ : ℝ) :
    continuedKernel t = bilateralSpectralKernel t φ φ :=
  (continuedKernel_initial t ht).trans (bilateralSpectralKernel_diagonal t φ ht).symm

/-- Every claimed half-integer is an actual simple pole, including the leading pole. -/
theorem circle_all_poles (m : ℕ) :
    meromorphicOrderAt continuedKernel (polePoint m) = (-1 : ℤ) ∧
    kernelResidue m ≠ 0 ∧
    Tendsto (fun t : ℂ => (t-polePoint m)*continuedKernel t)
      (𝓝[≠] polePoint m) (𝓝 (kernelResidue m)) :=
  ⟨continuedKernel_simple_pole m, kernelResidue_ne_zero m, continuedKernel_residue m⟩

/-- Source-normalized residue formula for the original kernel, not just a formal Bell coefficient. -/
theorem circle_residue_formula (m : ℕ) :
    Tendsto (fun t : ℂ => (t-(1/2-(m : ℂ)))*continuedKernel t)
      (𝓝[≠] (1/2-(m : ℂ)))
      (𝓝 ((1/(2*Real.pi : ℂ))*Complex.exp (-(spectralConstant : ℂ)/2)*
        Complex.exp ((spectralConstant : ℂ)*(m : ℂ))*
        (CircleResidues.residuePolynomial (1/2-(m : ℚ)) (2*m) : ℂ))) := by
  simpa only [polePoint, kernelResidue_source_formula] using continuedKernel_residue m

/-- Concrete original positive circle operator and both Fourier signs. -/
theorem circle_operator_fourier (n : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    circleOperator (fun w => w^n) z = (circleEigenvalue n : ℂ)*z^n ∧
    circleOperator (fun w => conj (w^n)) z = (circleEigenvalue n : ℂ)*conj (z^n) := by
  exact ⟨circleOperator_monomial n z hz, circleOperator_conjugate_monomial n z hz⟩

end CircleKernel
