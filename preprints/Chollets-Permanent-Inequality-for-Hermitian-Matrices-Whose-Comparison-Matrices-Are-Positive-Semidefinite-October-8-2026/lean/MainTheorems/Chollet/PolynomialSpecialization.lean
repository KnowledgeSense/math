import MainTheorems.Chollet.PencilCoefficients
import MainTheorems.Chollet.RankPolynomial

noncomputable section

open scoped ComplexOrder MatrixOrder

namespace ResearchMain.Chollet

variable {K : Type*}

def polynomialSpecialization (e : K → ℕ) :
    MvPolynomial K ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun k => Polynomial.X ^ e k)

theorem polynomialSpecialization_monomial (e : K → ℕ) (d : K →₀ ℕ) (a : ℂ) :
    polynomialSpecialization e (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ d.sum (fun k n => e k * n) := by
  classical
  simp only [polynomialSpecialization, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod, Finsupp.sum, ← pow_mul, Finset.prod_pow_eq_pow_sum]

theorem polynomialSpecialization_coeff_nonneg (e : K → ℕ) (p : MvPolynomial K ℂ)
    (hp : ∀ d, 0 ≤ (p.coeff d).re) (n : ℕ) :
    0 ≤ ((polynomialSpecialization e p).coeff n).re := by
  classical
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  simp only [Polynomial.finsetSum_coeff, Complex.re_sum]
  apply Finset.sum_nonneg
  intro d _
  rw [polynomialSpecialization_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  split_ifs <;> simp [hp]

theorem polynomialSpecialization_coeff_im_zero (e : K → ℕ) (p : MvPolynomial K ℂ)
    (hp : ∀ d, (p.coeff d).im = 0) (n : ℕ) :
    ((polynomialSpecialization e p).coeff n).im = 0 := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [Polynomial.finsetSum_coeff, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro d _
  rw [polynomialSpecialization_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  split_ifs <;> simp [hp]

theorem rankPolynomial_specialization (B : Matrix I I ℂ) (x : I → ℂ)
    [Fintype I] [DecidableEq I] :
    polynomialSpecialization (fun b : Bool => if b then 1 else 0)
      (pencilPolynomial (fun b : Bool => if b then rankOne x else B)) =
      rankPolynomial B x := by
  classical
  let P : Bool → Matrix I I ℂ := fun b => if b then rankOne x else B
  have h := permanent_map_ringHom
    (fun i j => ∑ b : Bool, MvPolynomial.C (P b i j) * MvPolynomial.X b)
    (polynomialSpecialization (fun b : Bool => if b then 1 else 0))
  change polynomialSpecialization _ (pencilPolynomial P) = _
  dsimp only [pencilPolynomial]
  rw [h]
  dsimp only [rankPolynomial]
  apply congrArg Matrix.permanent
  funext i j
  change polynomialSpecialization (fun b : Bool => if b then 1 else 0)
    (∑ b : Bool, MvPolynomial.C (P b i j) * MvPolynomial.X b) =
      Polynomial.C (B i j) + Polynomial.X * Polynomial.C (x i * star (x j))
  simp [P, polynomialSpecialization, rankOne, Matrix.vecMulVec, add_comm]
  ring

theorem rankCoefficient_nonneg (B : Matrix I I ℂ) (x : I → ℂ)
    [Fintype I] [DecidableEq I] (hB : B.PosSemidef) (n : ℕ) :
    0 ≤ rankCoefficient B x n := by
  have hP : ∀ b : Bool, (if b then rankOne x else B).PosSemidef := by
    intro b
    cases b
    · exact hB
    · exact rankOne_positiveSemidefinite x
  have h := polynomialSpecialization_coeff_nonneg
    (fun b : Bool => if b then 1 else 0) _
    (pencil_coeff_nonneg (fun b : Bool => if b then rankOne x else B) hP) n
  rw [rankPolynomial_specialization] at h
  exact h

theorem rankCoefficient_im_zero (B : Matrix I I ℂ) (x : I → ℂ)
    [Fintype I] [DecidableEq I] (hB : B.PosSemidef) (n : ℕ) :
    ((rankPolynomial B x).coeff n).im = 0 := by
  have hP : ∀ b : Bool, (if b then rankOne x else B).PosSemidef := by
    intro b
    cases b
    · exact hB
    · exact rankOne_positiveSemidefinite x
  have h := polynomialSpecialization_coeff_im_zero
    (fun b : Bool => if b then 1 else 0) _
    (pencil_coeff_im_zero (fun b : Bool => if b then rankOne x else B) hP) n
  rw [rankPolynomial_specialization] at h
  exact h

theorem rankPolynomial_coeff_real (B : Matrix I I ℂ) (x : I → ℂ)
    [Fintype I] [DecidableEq I] (hB : B.PosSemidef) (n : ℕ) :
    (rankPolynomial B x).coeff n = (rankCoefficient B x n : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using rankCoefficient_im_zero B x hB n

end ResearchMain.Chollet
