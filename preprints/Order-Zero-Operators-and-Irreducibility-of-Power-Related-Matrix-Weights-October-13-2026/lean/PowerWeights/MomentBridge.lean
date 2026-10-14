import PowerWeights.OperatorCoefficients
import PowerWeights.WeightPositivity

namespace PowerWeights

open Polynomial MeasureTheory
open scoped ComplexOrder

 theorem integrateMatrix_sub {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (P Q : PolynomialMatrix N) :
    integrateMatrix H (P-Q)=integrateMatrix H P-integrateMatrix H Q := by
  ext i j
  simp [integrateMatrix]

 theorem intertwining_from_moments {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (P : PolynomialMatrix N)
    (C₀ D : Matrix (Fin N) (Fin N) ℂ)
    (hm : ∀ n, C₀*moment I w P n=moment I w P n*D) :
    constant C₀*P=P*constant D := by
  let Z := constant C₀*P-P*constant D
  have hz : ∀ n, moment I w Z n=0 := by
    intro n
    rw [moment_as_integral H]
    dsimp [Z]
    rw [smul_sub,integrateMatrix_sub]
    rw [← Matrix.mul_smul,← Matrix.smul_mul,
      integrateMatrix_constant_left,integrateMatrix_constant_right,
      ← moment_as_integral H,hm n,sub_self]
  have hZ : Z=0 := by
    apply Matrix.ext
    intro i j
    apply polynomial_zero_of_weighted_moments H.open_interval H.nonempty_interval w
      (Z i j) H.positive (H.moment_integrable (Z i j))
    intro n
    exact congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) (hz n)
  exact sub_eq_zero.mp hZ

/-- The finite polynomial-moment bridge applied to the original orthogonal
polynomials, without a bounded-support or moment-determinacy assumption. -/
theorem order_zero_scalar {N : ℕ} (hN : 0<N) (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w)
    (Q : MonicOrthogonalSequence I w (polynomialWeight N s a))
    (B : PolynomialMatrix N) (hB : IsOrderZeroEigenoperator Q B) :
    ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  obtain ⟨C₀,hC,hcomm⟩ := eigenoperator_constant_and_commuting Q B hB
  let M := moment I w (polynomialWeight N s a)
  let D := (M 0)⁻¹*C₀*M 0
  have hu : IsUnit (M 0) := (zeroth_moment_posDef H a).isUnit
  let : Invertible (M 0) := hu.invertible
  have hz : C₀*M 0=M 0*D := by
    dsimp [D]
    simp only [← mul_assoc,Matrix.mul_inv_of_invertible,one_mul]
  have hm : ∀ n, C₀*M n=M n*D := moments_intertwine M Q.lower C₀ D hz
    (orthogonal_moment_recurrence H (polynomialWeight N s a) Q) hcomm
  have hpoly := intertwining_from_moments H (polynomialWeight N s a) C₀ D hm
  obtain ⟨c,hc⟩ := polynomial_intertwiner_scalar hN s a ha C₀ D hpoly
  exact ⟨c,hC.trans (congrArg constant hc)⟩

 theorem scalar_is_order_zero {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P) (c : ℂ) :
    IsOrderZeroEigenoperator Q (constant (c • (1 : Matrix (Fin N) (Fin N) ℂ))) := by
  intro n
  refine ⟨c • 1,?_⟩
  simp [constant_smul,constant_one]

 theorem order_zero_iff_scalar {N : ℕ} (hN : 0<N) (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w)
    (Q : MonicOrthogonalSequence I w (polynomialWeight N s a)) (B : PolynomialMatrix N) :
    IsOrderZeroEigenoperator Q B ↔
      ∃ c : ℂ, B=constant (c • (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  constructor
  · exact order_zero_scalar hN s a ha H Q B
  · rintro ⟨c,rfl⟩
    exact scalar_is_order_zero Q c

end PowerWeights
