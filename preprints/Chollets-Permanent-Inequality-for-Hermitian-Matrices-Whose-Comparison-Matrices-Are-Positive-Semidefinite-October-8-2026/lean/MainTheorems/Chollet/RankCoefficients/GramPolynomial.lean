import MainTheorems.Chollet.PolynomialSpecialization
import Mathlib.Algebra.Polynomial.Expand

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I J : Type*} [Fintype I] [Fintype J] [instI : DecidableEq I]

def augmentedColumns (Q : Matrix I J ℂ) (x : I → ℂ) : Matrix I (J ⊕ Unit) ℂ :=
  fun i => Sum.elim (Q i) (fun _ => x i)

def rankWeight : (J ⊕ Unit) → Unit →₀ ℕ :=
  Sum.elim (fun _ => 0) (fun _ => Finsupp.single () 1)

def assignmentDegree (f : I → J ⊕ Unit) : ℕ := (∑ i, rankWeight (f i)) ()

def assignmentPolynomial (Q : Matrix I J ℂ) (x : I → ℂ) : Polynomial ℂ :=
  ∑ f : I → J ⊕ Unit,
    Polynomial.C (((‖((augmentedColumns Q x).submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ)) *
      Polynomial.X ^ assignmentDegree f

omit [Fintype J] instI in
theorem rankWeight_sum_degree (f : I → J ⊕ Unit) :
    ((∑ i, rankWeight (f i)) + ∑ i, rankWeight (f i)).sum (fun _ n => 1 * n) =
      2 * assignmentDegree f := by
  rw [Finsupp.sum_fintype _ _ (by intro _; simp)]
  simp only [Finset.univ_unique, Finset.sum_singleton, Finsupp.add_apply, one_mul,
    assignmentDegree]
  change ((∑ i, rankWeight (f i)) ()) + ((∑ i, rankWeight (f i)) ()) =
    2 * ((∑ i, rankWeight (f i)) ())
  omega

omit [Fintype I] instI in
theorem specialized_weightedGram (Q : Matrix I J ℂ) (x : I → ℂ) :
    (weightedGram (augmentedColumns Q x) rankWeight).map
      (polynomialSpecialization (fun _ : Unit => 1)) =
      (fun i j => Polynomial.C ((Q * Q.conjTranspose) i j) +
        Polynomial.X ^ 2 * Polynomial.C (x i * star (x j))) := by
  funext i j
  simp [Matrix.map_apply, weightedGram, augmentedColumns, rankWeight,
    polynomialSpecialization, Fintype.sum_sum_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  ring

theorem rankPolynomial_expand_two (B : Matrix I I ℂ) (x : I → ℂ) :
    Polynomial.expand ℂ 2 (rankPolynomial B x) =
      Matrix.permanent (fun i j => Polynomial.C (B i j) +
        Polynomial.X ^ 2 * Polynomial.C (x i * star (x j))) := by
  let A : Matrix I I (Polynomial ℂ) := fun i j => Polynomial.C (B i j) +
    Polynomial.X * Polynomial.C (x i * star (x j))
  have h := permanent_map_ringHom A (Polynomial.expand ℂ 2).toRingHom
  change (Polynomial.expand ℂ 2).toRingHom A.permanent = _
  rw [h]
  apply congrArg Matrix.permanent
  funext i j
  change Polynomial.expand ℂ 2
      (Polynomial.C (B i j) + Polynomial.X * Polynomial.C (x i * star (x j))) = _
  simp only [map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]

theorem gram_assignment_polynomial (Q : Matrix I J ℂ) (x : I → ℂ) :
    Polynomial.C (Fintype.card (Equiv.Perm I) : ℂ) *
        rankPolynomial (Q * Q.conjTranspose) x = assignmentPolynomial Q x := by
  have h := congrArg (polynomialSpecialization (fun _ : Unit => 1))
    (permanent_weightedGram (augmentedColumns Q x) rankWeight)
  rw [map_mul, permanent_map_ringHom, specialized_weightedGram] at h
  have hn : polynomialSpecialization (fun _ : Unit => 1)
      (Fintype.card (Equiv.Perm I) : MvPolynomial Unit ℂ) =
      Polynomial.C (Fintype.card (Equiv.Perm I) : ℂ) := by simp
  rw [hn, ← rankPolynomial_expand_two] at h
  have hr : polynomialSpecialization (fun _ : Unit => 1)
      (∑ f : I → J ⊕ Unit,
        MvPolynomial.monomial ((∑ i, rankWeight (f i)) + ∑ i, rankWeight (f i))
          (((‖((augmentedColumns Q x).submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ))) =
      Polynomial.expand ℂ 2 (assignmentPolynomial Q x) := by
    simp only [map_sum, polynomialSpecialization_monomial, rankWeight_sum_degree,
      assignmentPolynomial, map_mul, map_pow, Polynomial.expand_C, Polynomial.expand_X,
      pow_mul]
  rw [hr] at h
  apply Polynomial.expand_injective (R := ℂ) (by decide : 0 < 2)
  simpa only [map_mul, Polynomial.expand_C] using h

end ResearchMain.Chollet.RankCoefficients
