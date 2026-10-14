import MainTheorems.Chollet.DoubledPencil

noncomputable section

namespace ResearchMain.Chollet

open MvPolynomial
open scoped ComplexOrder

def thirdShift : MvPolynomial (Fin 3) ℂ →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C ![1, 1, 1 + Polynomial.X]

theorem thirdShift_monomial (d : Fin 3 →₀ ℕ) (a : ℂ) :
    thirdShift (monomial d a) = Polynomial.C a * (1 + Polynomial.X) ^ d 2 := by
  rw [thirdShift, eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (by intro k; simp), Fin.prod_univ_three]
  simp

theorem thirdShift_coeff_zero (p : MvPolynomial (Fin 3) ℂ) :
    ((thirdShift p).coeff 0).re = ∑ d ∈ p.support, (p.coeff d).re := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [Polynomial.finsetSum_coeff, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [thirdShift_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  simp

theorem thirdShift_coeff_one (p : MvPolynomial (Fin 3) ℂ) :
    ((thirdShift p).coeff 1).re = ∑ d ∈ p.support, (d 2 : ℝ) * (p.coeff d).re := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [Polynomial.finsetSum_coeff, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [thirdShift_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  simp [Complex.mul_re, mul_comm]

theorem thirdShift_boost (p : MvPolynomial (Fin 3) ℂ) :
    (eval (fun _ => (1 : ℂ)) (polynomialBoost p 2)).re =
      ((thirdShift p).coeff 0).re + ((thirdShift p).coeff 1).re := by
  rw [polynomialBoost_eval_one, thirdShift_coeff_zero, thirdShift_coeff_one,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  push_cast
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem rankOne_squared (x : I → ℂ) :
    hadamard (rankOne x) (conjugate (rankOne x)) =
      rankOne (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ)) := by
  ext i j
  change (x i * star (x j)) * star (x i * star (x j)) =
    ((‖x i‖ ^ 2 : ℝ) : ℂ) * star ((‖x j‖ ^ 2 : ℝ) : ℂ)
  simp only [Complex.star_def, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  calc
    _ = (x i * (starRingEnd ℂ) (x i)) * (x j * (starRingEnd ℂ) (x j)) := by ring
    _ = _ := by simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem thirdShift_doubled (H : Matrix I I ℂ) (x : I → ℂ) :
    thirdShift (doubledPolynomial H x) =
      rankPolynomial (hadamard (pencil H x 1) (conjugate (pencil H x 1)))
        (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ)) := by
  let P := doubledPencils H x
  let A : Matrix I I (MvPolynomial (Fin 3) ℂ) := fun i j =>
    ∑ k, C (P k i j) * X k
  have h := permanent_map_ringHom A thirdShift
  change thirdShift A.permanent = _
  rw [h]
  apply congrArg Matrix.permanent
  funext i j
  change thirdShift (∑ k, C (P k i j) * X k) =
    Polynomial.C (hadamard (pencil H x 1) (conjugate (pencil H x 1)) i j) +
      Polynomial.X * Polynomial.C (rankOne (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ)) i j)
  rw [← rankOne_squared]
  rw [Fin.sum_univ_three]
  simp only [map_add, map_mul]
  simp only [thirdShift, eval₂Hom_C, eval₂Hom_X']
  change Polynomial.C (hadamard H (conjugate H) i j) * 1 +
      Polynomial.C (hadamard H (conjugate (rankOne x)) i j +
        hadamard (rankOne x) (conjugate H) i j) * 1 +
      Polynomial.C (hadamard (rankOne x) (conjugate (rankOne x)) i j) *
        (1 + Polynomial.X) = _
  have he : hadamard (pencil H x 1) (conjugate (pencil H x 1)) i j =
      hadamard H (conjugate H) i j +
        (hadamard H (conjugate (rankOne x)) i j +
          hadamard (rankOne x) (conjugate H) i j) +
        hadamard (rankOne x) (conjugate (rankOne x)) i j := by
    simp only [hadamard, conjugate, pencil, Matrix.add_apply,
      one_smul, star_add]
    ring
  rw [he]
  simp only [map_add]
  ring

theorem doubledPolynomial_first_bound {H : Matrix I I ℂ} (hH : H.PosSemidef)
    (x : I → ℂ) :
    (hadamard (pencil H x 1) (conjugate (pencil H x 1))).permanent.re +
      (rankFirst (hadamard (pencil H x 1) (conjugate (pencil H x 1)))
        (fun i => ((‖x i‖ ^ 2 : ℝ) : ℂ))).re ≤
      (hadamard (pencil H x (Real.sqrt 2))
        (conjugate (pencil H x (Real.sqrt 2)))).permanent.re := by
  have h := doubledPolynomial_boost_bound hH x
  rw [thirdShift_boost, thirdShift_doubled, rankPolynomial_coeff_zero,
    rankPolynomial_coeff_one] at h
  exact h

end ResearchMain.Chollet
