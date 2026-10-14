import MainTheorems.Chollet.RankPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

theorem polynomial_eq_of_nat_eval_eq (P Q : Polynomial ℂ)
    (h : ∀ n : ℕ, P.eval (n : ℂ) = Q.eval (n : ℂ)) : P = Q := by
  have hi : Function.Injective (fun n : ℕ => (n : ℂ)) := Nat.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.infinite_range_of_injective hi).mono (by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    exact h n)

theorem permanent_zero_row {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
    (A : Matrix I I R) (i : I) (h : ∀ j, A i j = 0) : A.permanent = 0 := by
  unfold Matrix.permanent
  apply Finset.sum_eq_zero
  intro e _
  apply Finset.prod_eq_zero (Finset.mem_univ (e.symm i))
  rw [Equiv.apply_symm_apply]
  exact h (e.symm i)

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rankPolynomial_zero_row (B : Matrix I I ℂ) (x : I → ℂ) (i : I)
    (hB : ∀ j, B i j = 0) (hx : x i = 0) : rankPolynomial B x = 0 := by
  apply permanent_zero_row _ i
  intro j
  simp only [hB j, hx, zero_mul, map_zero, mul_zero, add_zero]

theorem rankCoefficient_zero_row (B : Matrix I I ℂ) (x : I → ℂ) (i : I)
    (hB : ∀ j, B i j = 0) (hx : x i = 0) (k : ℕ) : rankCoefficient B x k = 0 := by
  rw [rankCoefficient, rankPolynomial_zero_row B x i hB hx]
  simp

theorem rankCoefficient_diagonal_zero (d : I → ℝ) (x : I → ℂ) (i : I)
    (hd : d i = 0) (hx : x i = 0) (k : ℕ) :
    rankCoefficient (Matrix.diagonal (fun i => (d i : ℂ))) x k = 0 := by
  apply rankCoefficient_zero_row _ x i _ hx k
  intro j
  by_cases hij : i = j
  · subst j
    simp [hd]
  · simp [hij]

end ResearchMain.Chollet.RankCoefficients
