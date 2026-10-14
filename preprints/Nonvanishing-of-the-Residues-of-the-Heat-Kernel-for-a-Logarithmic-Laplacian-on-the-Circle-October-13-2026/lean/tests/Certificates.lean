import CircleKernel

open CircleKernel Filter
open scoped Topology ComplexConjugate

example : circleEigenvalue 0 = 0 := circleEigenvalue_zero
example : circleEigenvalue 1 = 4 := by norm_num [circleEigenvalue, Finset.sum_range_succ]
example : complexResiduePolynomial 0 = 1 := complexResiduePolynomial_zero
example (j : ℕ) (hj : Odd j) : complexResiduePolynomial j = 0 := complexResiduePolynomial_odd j hj
example (n : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    circleOperator (fun w => w^n) z = (circleEigenvalue n : ℂ)*z^n :=
  (circle_operator_fourier n z hz).1
example (n : ℕ) (z : ℂ) (hz : ‖z‖=1) :
    circleOperator (fun w => conj (w^n)) z = (circleEigenvalue n : ℂ)*conj (z^n) :=
  (circle_operator_fourier n z hz).2
example (t : ℂ) (ht : 1/2 < t.re) (φ : ℝ) :
    continuedKernel t = bilateralSpectralKernel t φ φ := continuedKernel_bilateral_diagonal t ht φ
example : Meromorphic continuedKernel := continuedKernel_meromorphic
example (t : ℂ) : AnalyticAt ℂ continuedKernel t ↔ ∀ m : ℕ, t ≠ polePoint m :=
  continuedKernel_analyticAt_iff t
example (t : ℂ) : meromorphicOrderAt continuedKernel t < 0 ↔ ∃ m : ℕ, t=polePoint m :=
  continuedKernel_poles_iff t
example (m : ℕ) : meromorphicOrderAt continuedKernel (polePoint m) = (-1 : ℤ) :=
  (circle_all_poles m).1
example : meromorphicOrderAt continuedKernel (1/2) = (-1 : ℤ) := by
  simpa [polePoint] using continuedKernel_simple_pole 0
example (m : ℕ) : kernelResidue m ≠ 0 := (circle_all_poles m).2.1
example (m : ℕ) : Tendsto (fun t : ℂ => (t-polePoint m)*continuedKernel t)
    (𝓝[≠] polePoint m) (𝓝 (kernelResidue m)) := (circle_all_poles m).2.2
example (m : ℕ) : CircleResidues.residuePolynomial (1/2-m) (2*m) ≠ 0 :=
  CircleResidues.residuePolynomial_ne_zero m
example (m : ℕ) : padicValRat 2 (CircleResidues.residuePolynomial (1/2-m) (2*m)) =
    -3*(m : ℤ)-padicValNat 2 m.factorial := (CircleResidues.residuePolynomial_valuation m).2
