import PowerWeights.PositiveIntegral

namespace PowerWeights

open Polynomial MeasureTheory
open scoped ComplexOrder

 theorem evaluate_diagonal (N : ℕ) (s : Schedule) (x : ℝ) :
    evaluate (diagonal N s) x=Matrix.diagonal (fun i => (x : ℂ)^exponent s i.val) := by
  ext i j
  by_cases hij : i=j <;> simp [evaluate,diagonal,Matrix.diagonal,hij,
    Polynomial.eval_pow,Polynomial.eval_X]

 theorem weight_congruence (N : ℕ) (s : Schedule) (a : ℕ → ℝ) (w : ℝ → ℝ) (x : ℝ) :
    weight N s a w x=evaluate (factor N a) x *
      Matrix.diagonal (fun i : Fin N => ((w x*x^exponent s i.val : ℝ) : ℂ)) *
      (evaluate (factor N a) x).conjTranspose := by
  change (w x : ℂ) • evaluate (polynomialWeight N s a) x = _
  rw [polynomialWeight,evaluate_mul,evaluate_mul,evaluate_adjoint,evaluate_diagonal]
  have hd : (w x : ℂ) • Matrix.diagonal (fun i : Fin N => (x : ℂ)^exponent s i.val) =
      Matrix.diagonal (fun i : Fin N => ((w x*x^exponent s i.val : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal,Matrix.smul_apply,smul_eq_mul,
      hij,Complex.ofReal_mul,Complex.ofReal_pow]
  rw [← hd]
  simp

 theorem factor_evaluation_isUnit (N : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    IsUnit (evaluate (factor N a) x) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨evaluate (inverseFactor N a) x,?_⟩
  rw [← evaluate_mul]
  change evaluate (factor N a*(1-(X : ℂ[X]) • constant (pathMatrix N a))) x=1
  rw [factor_inverse_right,evaluate_one]

 theorem weight_positive_definite {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) :
    ∀ᵐ x ∂volume.restrict I, (weight N s a w x).PosDef := by
  have hp : ∀ᵐ x ∂volume.restrict I, ∀ i : Fin N, 0<w x*x^exponent s i.val :=
    (Filter.eventually_all).mpr H.powers_positive
  filter_upwards [hp] with x hx
  rw [weight_congruence]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (factor_evaluation_isUnit N a x)).mpr
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast hx i

 theorem zeroth_moment_posDef {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) :
    (moment I w (polynomialWeight N s a) 0).PosDef := by
  have hμ : volume.restrict I≠0 := by
    intro hh
    have hz := congrArg (fun μ : Measure ℝ => μ Set.univ) hh
    have hi0 : volume I=0 := by simpa using hz
    exact H.open_interval.measure_ne_zero volume H.nonempty_interval hi0
  have hi : ∀ i j : Fin N, Integrable (fun x => weight N s a w x i j) (volume.restrict I) := by
    intro i j
    simpa [weight,Matrix.smul_apply,smul_eq_mul] using
      H.polynomial_integrable (polynomialWeight N s a i j)
  have hp := integral_matrix_posDef hμ (weight N s a w) hi (weight_positive_definite H a)
  change Matrix.PosDef (fun i j => ∫ x in I,
    (w x : ℂ)*(x : ℂ)^0*(polynomialWeight N s a i j).eval (x : ℂ))
  simpa only [weight,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,pow_zero,mul_one] using hp

end PowerWeights
