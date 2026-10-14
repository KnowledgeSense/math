import PowerWeights.MeasureModel

noncomputable section

namespace PowerWeights

open Polynomial MeasureTheory

variable {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}

/-- Integration against the actual scalar weight is a linear functional on
finite polynomials; all its uses are justified by finite moments. -/
def polynomialIntegral (H : AdmissibleWeight N s I w) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun p := ∫ x in I, (w x : ℂ)*p.eval (x : ℂ)
  map_add' p q := by
    simp only [eval_add,mul_add]
    exact integral_add (H.polynomial_integrable p) (H.polynomial_integrable q)
  map_smul' z p := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring

def integrateMatrix (H : AdmissibleWeight N s I w) (P : PolynomialMatrix N) :
    Matrix (Fin N) (Fin N) ℂ := P.map (polynomialIntegral H)

 theorem integrateMatrix_add (H : AdmissibleWeight N s I w) (P Q : PolynomialMatrix N) :
    integrateMatrix H (P+Q)=integrateMatrix H P+integrateMatrix H Q := by
  ext i j
  simp [integrateMatrix]

 theorem integrateMatrix_sum {α : Type*} (H : AdmissibleWeight N s I w)
    (t : Finset α) (P : α → PolynomialMatrix N) :
    integrateMatrix H (∑ j ∈ t, P j)=∑ j ∈ t, integrateMatrix H (P j) := by
  ext i j
  simp [integrateMatrix,Matrix.sum_apply]

 theorem integrateMatrix_constant_left (H : AdmissibleWeight N s I w)
    (F : Matrix (Fin N) (Fin N) ℂ) (P : PolynomialMatrix N) :
    integrateMatrix H (constant F*P)=F*integrateMatrix H P := by
  ext i j
  simp only [integrateMatrix,Matrix.map_apply,Matrix.mul_apply,constant,map_sum,
    ← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]

 theorem integrateMatrix_constant_right (H : AdmissibleWeight N s I w)
    (F : Matrix (Fin N) (Fin N) ℂ) (P : PolynomialMatrix N) :
    integrateMatrix H (P*constant F)=integrateMatrix H P*F := by
  ext i j
  simp only [integrateMatrix,Matrix.map_apply,Matrix.mul_apply,constant,map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_comm,← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,mul_comm]

 theorem moment_as_integral (H : AdmissibleWeight N s I w) (P : PolynomialMatrix N) (n : ℕ) :
    moment I w P n=integrateMatrix H ((X : ℂ[X])^n • P) := by
  ext i j
  simp [moment,integrateMatrix,polynomialIntegral,Matrix.smul_apply,smul_eq_mul,
    eval_mul,eval_pow,eval_X,mul_assoc]

 theorem orthogonal_moment_recurrence (H : AdmissibleWeight N s I w)
    (P : PolynomialMatrix N) (Q : MonicOrthogonalSequence I w P) (n : ℕ) (hn : 0<n) :
    moment I w P n = -∑ j ∈ Finset.range n, Q.lower n j*moment I w P j := by
  have hz := Q.orthogonal n 0 hn
  rw [moment_as_integral H, pow_zero,one_smul,Q.monic,add_mul,Finset.sum_mul] at hz
  simp only [Matrix.smul_mul,one_mul] at hz
  rw [integrateMatrix_add,integrateMatrix_sum] at hz
  simp_rw [← Matrix.mul_smul,integrateMatrix_constant_left,← moment_as_integral H] at hz
  exact eq_neg_of_add_eq_zero_left hz

end PowerWeights
