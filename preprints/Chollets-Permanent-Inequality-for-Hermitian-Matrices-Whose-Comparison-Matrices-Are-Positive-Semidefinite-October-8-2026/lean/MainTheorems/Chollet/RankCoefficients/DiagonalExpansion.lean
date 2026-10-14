import MainTheorems.Chollet.RankCoefficients.PermanentCoefficient
import MainTheorems.Chollet.RankCoefficients.PowerCoefficient
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

open MvPolynomial

variable {I : Type*} [Fintype I] [DecidableEq I]

def rowLinearPolynomial (x : I → ℂ) : MvPolynomial I ℂ := ∑ i, C (x i) * X i

theorem exponent_complement (s : Finset I) :
    exponent s + exponent (Finset.univ \ s) = exponent (Finset.univ : Finset I) := by
  ext i
  simp only [Finsupp.add_apply, exponent_apply, Finset.mem_univ, ite_true,
    Finset.mem_sdiff, true_and]
  by_cases hi : i ∈ s <;> simp [hi]

omit [Fintype I] [DecidableEq I] in
theorem polynomial_variables (s : Finset I) :
    (∏ i ∈ s, (X i : MvPolynomial I ℂ)) = MvPolynomial.monomial (exponent s) 1 := by
  rw [exponent, MvPolynomial.monomial_sum_one]
  rfl

theorem diagonal_term_coefficient (x u d : I → ℂ) (s : Finset I) :
    ((∏ i ∈ s, C (u i) * rowLinearPolynomial x) *
      ∏ i ∈ Finset.univ \ s, C (d i) * X i).coeff
        (exponent (Finset.univ : Finset I)) =
      (s.card.factorial : ℂ) * (∏ i ∈ s, u i) * (∏ i ∈ s, x i) *
        ∏ i ∈ Finset.univ \ s, d i := by
  have he : (∏ i ∈ s, C (u i) * rowLinearPolynomial x) *
      (∏ i ∈ Finset.univ \ s, C (d i) * X i) =
      C ((∏ i ∈ s, u i) * ∏ i ∈ Finset.univ \ s, d i) *
        (rowLinearPolynomial x ^ s.card * MvPolynomial.monomial
          (exponent (Finset.univ \ s)) 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← map_prod, ← map_prod, Finset.prod_const, polynomial_variables]
    rw [map_mul]
    ring
  rw [he, coeff_C_mul, ← exponent_complement s, coeff_mul_monomial]
  change _ * (((∑ i, C (x i) * X i : MvPolynomial I ℂ) ^ s.card).coeff (exponent s) * 1) = _
  rw [linearPower_coeff, ite_eq_left rfl, mul_one]
  ring

theorem columnProduct_diagonal_rank (d x : I → ℂ) (s : ℂ) :
    columnProduct (fun i j => Matrix.diagonal d i j + s * (x i * star (x j))) =
      ∏ j, (C (s * star (x j)) * rowLinearPolynomial x + C (d j) * X j) := by
  unfold columnProduct
  apply Finset.prod_congr rfl
  intro j _
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  have hd : (∑ i, C (Matrix.diagonal d i j) * X i) = C (d j) * X j := by
    simp only [Matrix.diagonal_apply, apply_ite, map_zero, ite_mul, zero_mul]
    simpa only [Finset.mem_univ, ite_true] using
      Finset.sum_ite_eq' Finset.univ j (fun i => C (d i) * X i)
  rw [hd]
  have hr : (∑ i, C (s * (x i * star (x j))) * X i) =
      C (s * star (x j)) * rowLinearPolynomial x := by
    unfold rowLinearPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show s * (x i * star (x j)) = (s * star (x j)) * x i by ring, map_mul]
    ring
  rw [hr, add_comm]

theorem permanent_diagonal_rank (d x : I → ℂ) (s : ℂ) :
    Matrix.permanent (fun i j => Matrix.diagonal d i j + s * (x i * star (x j))) =
      ∑ t ∈ (Finset.univ : Finset I).powerset,
        (t.card.factorial : ℂ) * s ^ t.card *
          (∏ i ∈ t, ((‖x i‖ ^ 2 : ℝ) : ℂ)) *
          ∏ i ∈ Finset.univ \ t, d i := by
  let A : Matrix I I ℂ := fun i j => Matrix.diagonal d i j + s * (x i * star (x j))
  change A.permanent = _
  rw [← permanent_coefficient A]
  change (columnProduct (fun i j => Matrix.diagonal d i j + s * (x i * star (x j)))).coeff _ = _
  rw [columnProduct_diagonal_rank, Finset.prod_add, coeff_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [diagonal_term_coefficient]
  have hu : (∏ i ∈ t, s * star (x i)) = s ^ t.card * ∏ i ∈ t, star (x i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hx : (∏ i ∈ t, star (x i)) * (∏ i ∈ t, x i) =
      ∏ i ∈ t, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simpa only [Complex.star_def, mul_comm] using (Complex.mul_conj (x i)).trans
      (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq (x i)))
  rw [hu]
  calc
    (t.card.factorial : ℂ) * (s ^ t.card * ∏ i ∈ t, star (x i)) *
        (∏ i ∈ t, x i) * (∏ i ∈ Finset.univ \ t, d i) =
      (t.card.factorial : ℂ) * s ^ t.card *
        ((∏ i ∈ t, star (x i)) * ∏ i ∈ t, x i) *
        ∏ i ∈ Finset.univ \ t, d i := by ring
    _ = _ := by rw [hx]

end ResearchMain.Chollet.RankCoefficients

