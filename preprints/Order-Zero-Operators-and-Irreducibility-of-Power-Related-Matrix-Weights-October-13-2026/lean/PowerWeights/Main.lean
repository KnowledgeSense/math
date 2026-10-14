import PowerWeights.OrthogonalExistence
import PowerWeights.MomentBridge
import PowerWeights.Irreducibility

noncomputable section
namespace PowerWeights

/-- Order-zero membership for the actual, explicitly constructed monic
orthogonal-polynomial sequence of the admissible matrix weight. -/
def InOrderZeroAlgebra (H : AdmissibleWeight N s I w) (a : ℕ → ℝ)
    (B : PolynomialMatrix N) : Prop :=
  IsOrderZeroEigenoperator (orthogonalSequence H a) B

/-- The full order-zero algebra is the complex scalar matrices, for every
positive size and both exponent conventions. -/
theorem order_zero_algebra_eq_scalars {N : ℕ} (hN : 0<N) (s : Schedule)
    (a : ℕ → ℝ) (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (B : PolynomialMatrix N) :
    InOrderZeroAlgebra H a B ↔
      ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
  order_zero_iff_scalar hN s a ha H (orthogonalSequence H a) B

/-- Original matrix-weight theorem, including existence of the monic
orthogonal polynomials and independence of their choice. -/
theorem power_relation_weight_theorem {N : ℕ} (hN : 0<N) (s : Schedule)
    (a : ℕ → ℝ) (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) :
    Nonempty (MonicOrthogonalSequence I w (polynomialWeight N s a)) ∧
    (∀ Q : MonicOrthogonalSequence I w (polynomialWeight N s a),
      ∀ B : PolynomialMatrix N, IsOrderZeroEigenoperator Q B ↔
        ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin N) (Fin N) ℂ))) ∧
    (∀ F : Matrix (Fin N) (Fin N) ℂ,
      WeightSymmetric I (weight N s a w) F ↔
        ∃ c : ℝ, F=(c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) ∧
    ¬ReducibleByConstantCongruence I (weight N s a w) := by
  exact ⟨monic_orthogonal_sequence_exists H a,
    order_zero_iff_scalar hN s a ha H,
    weight_symmetric_iff_real_scalar hN s a ha H,
    not_reducible_by_constant_congruence hN s a ha H⟩

end PowerWeights
