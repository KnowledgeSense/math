import PowerWeights.ScalarMoments
import PowerWeights.IntertwiningClassification
import Mathlib.Analysis.Matrix.PosDef

noncomputable section

namespace PowerWeights

open Polynomial MeasureTheory

/-- Admissibility of the common scalar weight on a nonempty open domain.
In particular, all nonempty open intervals, including unbounded ones, are covered. -/
structure AdmissibleWeight (N : ℕ) (s : Schedule) (I : Set ℝ) (w : ℝ → ℝ) : Prop where
  open_interval : IsOpen I
  nonempty_interval : I.Nonempty
  positive : ∀ᵐ x ∂volume.restrict I, 0<w x
  powers_positive : ∀ i : Fin N, ∀ᵐ x ∂volume.restrict I, 0<w x*x^exponent s i.val
  moments : ∀ n, Integrable (fun x : ℝ => w x*x^n) (volume.restrict I)

/-- Entrywise polynomial evaluation at a real argument. -/
def evaluate {N : ℕ} (P : PolynomialMatrix N) (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  P.map (Polynomial.eval (x : ℂ))

/-- Coefficient matrices of a matrix polynomial. -/
def coefficient {N : ℕ} (P : PolynomialMatrix N) (n : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (P i j).coeff n

/-- Actual entrywise weighted moments of a polynomial matrix. -/
def moment {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ) (P : PolynomialMatrix N) (n : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∫ x in I, (w x : ℂ)*(x : ℂ)^n*(P i j).eval (x : ℂ)

/-- A monic matrix orthogonal-polynomial sequence for the actual weight `wP`.
The monic normal form records the actual coefficient matrices. Orthogonality
is against every lower monomial, the usual equivalent defining condition. -/
structure MonicOrthogonalSequence {N : ℕ} (I : Set ℝ) (w : ℝ → ℝ)
    (P : PolynomialMatrix N) where
  Q : ℕ → PolynomialMatrix N
  lower : ℕ → ℕ → Matrix (Fin N) (Fin N) ℂ
  monic : ∀ n, Q n=(X : ℂ[X])^n • 1 +
    ∑ j ∈ Finset.range n, (X : ℂ[X])^j • constant (lower n j)
  orthogonal : ∀ n m, m<n → moment I w (Q n*P) m=0

/-- A right-acting order-zero polynomial differential eigenoperator. -/
def IsOrderZeroEigenoperator {N : ℕ} {I : Set ℝ} {w : ℝ → ℝ}
    {P : PolynomialMatrix N} (Q : MonicOrthogonalSequence I w P)
    (B : PolynomialMatrix N) : Prop :=
  ∀ n, ∃ Λ : Matrix (Fin N) (Fin N) ℂ, Q.Q n*B=constant Λ*Q.Q n

 theorem integrable_weighted_polynomial {μ : Measure ℝ} (w : ℝ → ℝ)
    (hm : ∀ n, Integrable (fun x : ℝ => (w x : ℂ)*(x : ℂ)^n) μ)
    (p : ℂ[X]) : Integrable (fun x : ℝ => (w x : ℂ)*p.eval (x : ℂ)) μ := by
  have hi : Integrable (fun x : ℝ => ∑ j ∈ p.support,
      p.coeff j*((w x : ℂ)*(x : ℂ)^j)) μ :=
    integrable_finsetSum _ fun j _ => (hm j).const_mul _
  apply hi.congr
  filter_upwards [] with x
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring


 theorem AdmissibleWeight.complex_moments {N : ℕ} {s : Schedule} {I : Set ℝ}
    {w : ℝ → ℝ} (H : AdmissibleWeight N s I w) (n : ℕ) :
    Integrable (fun x : ℝ => (w x : ℂ)*(x : ℂ)^n) (volume.restrict I) := by
  have hi : Integrable (fun x : ℝ => ((w x*x^n : ℝ) : ℂ)) (volume.restrict I) :=
    (H.moments n).ofReal
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using hi

 theorem AdmissibleWeight.polynomial_integrable {N : ℕ} {s : Schedule} {I : Set ℝ}
    {w : ℝ → ℝ} (H : AdmissibleWeight N s I w) (p : ℂ[X]) :
    Integrable (fun x : ℝ => (w x : ℂ)*p.eval (x : ℂ)) (volume.restrict I) :=
  integrable_weighted_polynomial w H.complex_moments p

 theorem AdmissibleWeight.moment_integrable {N : ℕ} {s : Schedule} {I : Set ℝ}
    {w : ℝ → ℝ} (H : AdmissibleWeight N s I w) (p : ℂ[X]) (n : ℕ) :
    Integrable (fun x : ℝ => (w x : ℂ)*(x : ℂ)^n*p.eval (x : ℂ)) (volume.restrict I) := by
  apply (H.polynomial_integrable (X^n*p)).congr
  filter_upwards [] with x
  rw [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
  ring

@[simp] theorem evaluate_mul {N : ℕ} (P Q : PolynomialMatrix N) (x : ℝ) :
    evaluate (P*Q) x=evaluate P x*evaluate Q x :=
  ((Polynomial.evalRingHom (x : ℂ)).mapMatrix).map_mul P Q

@[simp] theorem evaluate_constant {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ) :
    evaluate (constant F) x=F := by
  ext i j
  simp [evaluate,constant]

@[simp] theorem evaluate_one (N : ℕ) (x : ℝ) :
    evaluate (1 : PolynomialMatrix N) x=1 :=
  ((Polynomial.evalRingHom (x : ℂ)).mapMatrix).map_one

 theorem evaluate_adjoint {N : ℕ} (P : PolynomialMatrix N) (x : ℝ) :
    evaluate (adjoint P) x=(evaluate P x).conjTranspose := by
  ext i j
  simp only [evaluate,adjoint,Matrix.map_apply,Matrix.conjTranspose_apply]
  simpa [conjugate] using
    (Polynomial.eval_map_apply (p := P j i) (starRingEnd ℂ) (x : ℂ))


end PowerWeights
