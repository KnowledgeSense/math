import PowerWeights.PolynomialGram
import PowerWeights.MatrixIntegration

noncomputable section
namespace PowerWeights
open Polynomial MeasureTheory Matrix
open scoped ComplexOrder

 theorem moment_monomial (H : AdmissibleWeight N s I w)
    (P : PolynomialMatrix N) (m j : ℕ) :
    moment I w ((X : ℂ[X])^j • P) m=moment I w P (m+j) := by
  rw [moment_as_integral H,moment_as_integral H,smul_smul,pow_add]

 theorem moment_constant_left (H : AdmissibleWeight N s I w)
    (P : PolynomialMatrix N) (F : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) :
    moment I w (constant F*P) m=F*moment I w P m := by
  rw [moment_as_integral H,← Matrix.mul_smul,integrateMatrix_constant_left,
    ← moment_as_integral H]

 theorem moment_add (H : AdmissibleWeight N s I w)
    (P Q : PolynomialMatrix N) (m : ℕ) :
    moment I w (P+Q) m=moment I w P m+moment I w Q m := by
  simp only [moment_as_integral H,smul_add,integrateMatrix_add]

 theorem moment_sum (H : AdmissibleWeight N s I w)
    (P : ℕ → PolynomialMatrix N) (n m : ℕ) :
    moment I w (∑ j ∈ Finset.range n,P j) m=
      ∑ j ∈ Finset.range n,moment I w (P j) m := by
  simp only [moment_as_integral H,Finset.smul_sum,integrateMatrix_sum]

 def leadingMoments {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ) (P : PolynomialMatrix N) (n : ℕ) :
    Matrix (Fin N) (Fin n × Fin N) ℂ :=
  fun r jt => moment I w P (n+jt.1.val) r jt.2

 def solvedRows {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ) (P : PolynomialMatrix N) (n : ℕ) :
    Matrix (Fin N) (Fin n × Fin N) ℂ :=
  -leadingMoments I w P n * (polynomialGram I w P n)⁻¹

 def solvedLower {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ) (P : PolynomialMatrix N)
    (n j : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun r t => if hj : j<n then solvedRows I w P n r (⟨j,hj⟩,t) else 0

 theorem solvedRows_equation (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) (n : ℕ) :
    solvedRows I w (polynomialWeight N s a) n *
      polynomialGram I w (polynomialWeight N s a) n =
      -leadingMoments I w (polynomialWeight N s a) n := by
  let G := polynomialGram I w (polynomialWeight N s a) n
  let : Invertible G := (polynomialGram_posDef H a n).isUnit.invertible
  change (-leadingMoments I w (polynomialWeight N s a) n * G⁻¹)*G = _
  rw [Matrix.mul_assoc,Matrix.inv_mul_of_invertible,Matrix.mul_one]

 theorem solvedLower_equation (H : AdmissibleWeight N s I w) (a : ℕ → ℝ)
    (n m : ℕ) (hm : m<n) :
    moment I w (polynomialWeight N s a) (n+m)+
      ∑ j ∈ Finset.range n, solvedLower I w (polynomialWeight N s a) n j *
        moment I w (polynomialWeight N s a) (j+m)=0 := by
  ext r t
  have he := congrArg (fun M => M r (⟨m,hm⟩,t)) (solvedRows_equation H a n)
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,polynomialGram,
    leadingMoments,Matrix.neg_apply] at he
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.mul_apply,Matrix.zero_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [solvedLower, dite_eq_left (Fin.is_lt _)]
  exact add_eq_zero_iff_eq_neg.mpr he |> fun hh => by simpa only [add_comm] using hh

/-- Direct finite Gram-system construction of the original monic orthogonal
matrix polynomials. The domain may be unbounded. -/
def orthogonalSequence (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) :
    MonicOrthogonalSequence I w (polynomialWeight N s a) where
  Q n := (X : ℂ[X])^n • 1 + ∑ j ∈ Finset.range n,
    (X : ℂ[X])^j • constant (solvedLower I w (polynomialWeight N s a) n j)
  lower := solvedLower I w (polynomialWeight N s a)
  monic _ := rfl
  orthogonal n m hm := by
    simp only [add_mul,Finset.sum_mul,Matrix.smul_mul,one_mul]
    rw [moment_add H,moment_sum H,moment_monomial H]
    simp_rw [moment_monomial H,moment_constant_left H]
    simpa only [Nat.add_comm] using solvedLower_equation H a n m hm

 theorem monic_orthogonal_sequence_exists (H : AdmissibleWeight N s I w) (a : ℕ → ℝ) :
    Nonempty (MonicOrthogonalSequence I w (polynomialWeight N s a)) :=
  ⟨orthogonalSequence H a⟩

end PowerWeights
