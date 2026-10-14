import PowerWeights.WeightPositivity
import PowerWeights.OperatorCoefficients

noncomputable section

namespace PowerWeights

open Polynomial MeasureTheory Matrix
open scoped ComplexOrder

 theorem polynomial_eval_ne_zero_ae {μ : Measure ℝ} [NullSingletonClass μ]
    (p : ℂ[X]) (hp : p≠0) : ∀ᵐ x : ℝ ∂μ, p.eval (x : ℂ)≠0 := by
  have hs : Set.Finite {x : ℝ | p.eval (x : ℂ)=0} :=
    (Polynomial.finite_setOfPred_isRoot hp).preimage Complex.ofReal_injective.injOn
  apply ae_iff.mpr
  simpa only [not_not] using hs.measure_zero (μ := μ)

/-- Evaluation of the degree-bounded column-polynomial basis. -/
def polynomialBasis (n N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin n × Fin N) ℂ :=
  fun r jt => if r=jt.2 then (x : ℂ)^jt.1.val else 0

def coordinatePolynomial {n N : ℕ} (v : Fin n × Fin N → ℂ) (r : Fin N) : ℂ[X] :=
  ∑ j : Fin n, C (v (j,r))*X^j.val

 theorem coordinatePolynomial_coeff {n N : ℕ} (v : Fin n × Fin N → ℂ)
    (r : Fin N) (i : Fin n) : (coordinatePolynomial v r).coeff i.val=v (i,r) := by
  simp only [coordinatePolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  simp_rw [← Fin.ext_iff]
  simp

 theorem basis_mulVec {n N : ℕ} (v : Fin n × Fin N → ℂ) (r : Fin N) (x : ℝ) :
    (polynomialBasis n N x *ᵥ v) r=(coordinatePolynomial v r).eval (x : ℂ) := by
  simp only [polynomialBasis,mulVec,dotProduct,Fintype.sum_prod_type,coordinatePolynomial,
    Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_C]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro j hj
  ring

 theorem basis_mulVec_ne_zero_ae {n N : ℕ} {μ : Measure ℝ} [NullSingletonClass μ]
    (v : Fin n × Fin N → ℂ) (hv : v≠0) :
    ∀ᵐ x : ℝ ∂μ, polynomialBasis n N x *ᵥ v≠0 := by
  obtain ⟨ir,hir⟩ : ∃ ir, v ir≠0 := Function.ne_iff.mp hv
  have hp : coordinatePolynomial v ir.2≠0 := by
    intro hh
    have hc := congrArg (fun p : ℂ[X] => p.coeff ir.1.val) hh
    rw [coordinatePolynomial_coeff] at hc
    exact hir hc
  filter_upwards [polynomial_eval_ne_zero_ae (μ := μ) _ hp] with x hx
  intro hz
  have hc := congrArg (fun v : Fin N → ℂ => v ir.2) hz
  rw [basis_mulVec] at hc
  exact hx hc

/-- The finite block-Hankel Gram matrix of all row-polynomial coefficients
below degree `n`, formed from the actual matrix-weight moments. -/
def polynomialGram {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ) (P : PolynomialMatrix N) (n : ℕ) :
    Matrix (Fin n × Fin N) (Fin n × Fin N) ℂ :=
  fun ir jt => moment I w P (ir.1.val+jt.1.val) ir.2 jt.2

def gramIntegrand {N : ℕ} (W : ℝ → Matrix (Fin N) (Fin N) ℂ) (n : ℕ) (x : ℝ) :
    Matrix (Fin n × Fin N) (Fin n × Fin N) ℂ :=
  fun ir jt => (x : ℂ)^(ir.1.val+jt.1.val)*W x ir.2 jt.2

 theorem gramIntegrand_congruence {N : ℕ} (W : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (n : ℕ) (x : ℝ) : gramIntegrand W n x=
      (polynomialBasis n N x).conjTranspose*W x*polynomialBasis n N x := by
  ext ir jt
  simp [gramIntegrand,polynomialBasis,Matrix.mul_apply,Matrix.conjTranspose_apply,
    apply_ite, pow_add,mul_assoc,mul_comm]

 theorem polynomialGram_posDef {N : ℕ} {s : Schedule} {I : Set ℝ} {w : ℝ → ℝ}
    (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) (n : ℕ) :
    (polynomialGram I w (polynomialWeight N s a) n).PosDef := by
  let W := weight N s a w
  let G := gramIntegrand W n
  have hμ : volume.restrict I≠0 := by
    intro hh
    have hz := congrArg (fun μ : Measure ℝ => μ Set.univ) hh
    have hi0 : volume I=0 := by simpa using hz
    exact H.open_interval.measure_ne_zero volume H.nonempty_interval hi0
  have hint : ∀ i j : Fin n × Fin N,
      Integrable (fun x => G x i j) (volume.restrict I) := by
    intro ir jt
    apply (H.moment_integrable (polynomialWeight N s a ir.2 jt.2)
      (ir.1.val+jt.1.val)).congr
    filter_upwards [] with x
    dsimp [G,gramIntegrand,W,weight]
    ring
  have hHerm : ∀ᵐ x ∂volume.restrict I, (G x).IsHermitian := by
    filter_upwards [weight_positive_definite H a] with x hx
    rw [show G x=gramIntegrand W n x from rfl,gramIntegrand_congruence]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hx.isHermitian
  have hquad : ∀ v : Fin n × Fin N → ℂ, v≠0 →
      ∀ᵐ x ∂volume.restrict I, 0<star v ⬝ᵥ (G x *ᵥ v) := by
    intro v hv
    filter_upwards [weight_positive_definite H a,basis_mulVec_ne_zero_ae v hv] with x hx hxv
    have hp := hx.dotProduct_mulVec_pos hxv
    rw [show G x=gramIntegrand W n x from rfl,gramIntegrand_congruence]
    simpa only [star_mulVec,dotProduct_mulVec,vecMul_vecMul] using hp
  have hpd := integral_matrix_posDef_of_quadratic hμ G hint hHerm hquad
  have he : polynomialGram I w (polynomialWeight N s a) n =
      (fun i j => ∫ x in I, G x i j) := by
    ext ir jt
    simp only [polynomialGram,moment,G,gramIntegrand,W,weight,Matrix.smul_apply,
      Matrix.map_apply,smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [he]
  exact hpd

end PowerWeights
