import MainTheorems.Chollet.PencilBoost
import MainTheorems.Chollet.SchurReduction
import MainTheorems.Chollet.RankPolynomial
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace ResearchMain.Chollet

open MvPolynomial
open scoped ComplexOrder

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]

theorem pencilPolynomial_eval (P : K → Matrix I I ℂ) (w : K → ℂ) :
    eval w (pencilPolynomial P) =
      Matrix.permanent (fun i j => ∑ k, P k i j * w k) := by
  let A : Matrix I I (MvPolynomial K ℂ) := fun i j => ∑ k, C (P k i j) * X k
  have h := permanent_map_ringHom A (eval w)
  change eval w A.permanent = _
  rw [h]
  apply congrArg Matrix.permanent
  funext i j
  change eval w (∑ k, C (P k i j) * X k) = _
  simp only [map_sum, map_mul, eval_C, eval_X]

omit [Fintype K] in
def doubledPencils (H : Matrix I I ℂ) (x : I → ℂ) : Fin 3 → Matrix I I ℂ :=
  ![hadamard H (conjugate H),
    hadamard H (conjugate (rankOne x)) + hadamard (rankOne x) (conjugate H),
    hadamard (rankOne x) (conjugate (rankOne x))]

omit [Fintype K] in
def doubledPolynomial (H : Matrix I I ℂ) (x : I → ℂ) : MvPolynomial (Fin 3) ℂ :=
  pencilPolynomial (doubledPencils H x)

omit [Fintype K] [DecidableEq I] in
theorem doubledPencils_positive {H : Matrix I I ℂ} (hH : H.PosSemidef) (x : I → ℂ)
    (k : Fin 3) : (doubledPencils H x k).PosSemidef := by
  have hP := rankOne_positiveSemidefinite x
  fin_cases k
  · exact hadamard_positiveSemidefinite hH (conjugate_positiveSemidefinite hH)
  · exact (hadamard_positiveSemidefinite hH (conjugate_positiveSemidefinite hP)).add
      (hadamard_positiveSemidefinite hP (conjugate_positiveSemidefinite hH))
  · exact hadamard_positiveSemidefinite hP (conjugate_positiveSemidefinite hP)

omit [Fintype K] in
theorem doubledPolynomial_coeff_nonneg {H : Matrix I I ℂ} (hH : H.PosSemidef)
    (x : I → ℂ) (d : Fin 3 →₀ ℕ) : 0 ≤ ((doubledPolynomial H x).coeff d).re :=
  pencil_coeff_nonneg (doubledPencils H x) (doubledPencils_positive hH x) d

omit [Fintype K] in
theorem doubledPolynomial_eval (H : Matrix I I ℂ) (x : I → ℂ) (t : ℝ) :
    eval ![1, (t : ℂ), (t : ℂ) ^ 2] (doubledPolynomial H x) =
      (hadamard (pencil H x t) (conjugate (pencil H x t))).permanent := by
  rw [doubledPolynomial, pencilPolynomial_eval]
  apply congrArg Matrix.permanent
  funext i j
  simp only [Fin.sum_univ_three]
  change H i j * star (H i j) * 1 +
      (H i j * star (rankOne x i j) + rankOne x i j * star (H i j)) * (t : ℂ) +
      (rankOne x i j * star (rankOne x i j)) * (t : ℂ) ^ 2 =
    (H i j + t • rankOne x i j) * star (H i j + t • rankOne x i j)
  simp only [Complex.real_smul, star_add, star_mul, Complex.star_def,
    Complex.conj_ofReal, mul_one]
  ring

def doubledWeights : Fin 3 → ℝ := ![1, Real.sqrt 2, 2]

theorem nat_successor_le_two_pow (n : ℕ) : (1 + n : ℕ) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast at ih ⊢
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem doubledWeights_bound (d : Fin 3 →₀ ℕ) :
    (1 + d 2 : ℕ) ≤ d.prod (fun k n => doubledWeights k ^ n) := by
  rw [Finsupp.prod_fintype _ _ (by intro k; simp), Fin.prod_univ_three]
  simp only [doubledWeights, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, one_pow, one_mul]
  have hs : 1 ≤ Real.sqrt 2 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  exact (nat_successor_le_two_pow (d 2)).trans
    (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hs))

omit [Fintype K] in
theorem doubledPolynomial_boost_bound {H : Matrix I I ℂ} (hH : H.PosSemidef)
    (x : I → ℂ) :
    (eval (fun _ => (1 : ℂ)) (polynomialBoost (doubledPolynomial H x) 2)).re ≤
      (hadamard (pencil H x (Real.sqrt 2))
        (conjugate (pencil H x (Real.sqrt 2)))).permanent.re := by
  have h := polynomialBoost_bound (doubledPolynomial H x) 2 doubledWeights
    (doubledPolynomial_coeff_nonneg hH x) doubledWeights_bound
  have hw : (fun k => (doubledWeights k : ℂ)) =
      ![1, (Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ) ^ 2] := by
    funext k
    fin_cases k <;> simp [doubledWeights, ← Complex.ofReal_pow, Real.sq_sqrt]
  rw [hw, doubledPolynomial_eval] at h
  exact h

end ResearchMain.Chollet
