import HilbertBipartite

open HilbertBipartite MvPolynomial Polynomial Finset

/-- The original theorem applies uniformly over every field. -/
example (K : Type*) [Field K] (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ReleaseMainTheorem K p q := release_main_theorem K p q hp hpq

/-- The four-cycle is a nonempty negative-coefficient case. -/
example (K : Type*) [Field K] : ReleaseMainTheorem K 2 2 :=
  release_main_theorem K 2 2 (by omega) (by omega)

example : hilbertCoefficient 2 2 0 = 16 := by
  rw [hilbertCoefficient_zero]
  norm_num

example : hilbertCoefficient 2 2 1 = 12 := by
  rw [hilbertCoefficient_low 2 2 1 (by omega) (by omega)]
  norm_num

example : hilbertCoefficient 2 2 2 = 1 := by
  rw [hilbertCoefficient_low 2 2 2 (by omega) (by omega)]
  norm_num

example : hilbertCoefficient 2 2 3 = -2 := by
  rw [hilbertCoefficient_eq_formula 2 2 3 (by omega) (by omega)]
  norm_num [coefficientFormula, weightedCoeff, delta, Finset.sum_filter,
    Finset.sum_range_succ, Polynomial.coeff_C_mul, Polynomial.coeff_mul, pow_two]

example : hilbertCoefficient 2 2 4 = 0 :=
  hilbertCoefficient_high 2 2 4 (by omega) (by omega) (by omega)

example (K : Type*) [Field K] :
    Module.length (MvPolynomial (Fin 2 ⊕ Fin 2) K)
      (MvPolynomial (Fin 2 ⊕ Fin 2) K ⧸ bipartiteIdeal K 2 2 ^ 1) = 7 := by
  rw [compositionLength_formula K 2 2 1 (by omega) (by omega) (by omega)]
  norm_num [correction, Finset.sum_range_succ, Finset.sum_Icc_succ_top, Nat.choose]

example (K : Type*) [Field K] :
    Module.length (MvPolynomial (Fin 2 ⊕ Fin 2) K)
      (MvPolynomial (Fin 2 ⊕ Fin 2) K ⧸ bipartiteIdeal K 2 2 ^ 2) = 39 := by
  rw [compositionLength_formula K 2 2 2 (by omega) (by omega) (by omega)]
  norm_num [correction, Finset.sum_range_succ, Finset.sum_Icc_succ_top, Nat.choose]

example (K : Type*) [Field K] :
    Module.length (MvPolynomial (Fin 2 ⊕ Fin 2) K)
      (MvPolynomial (Fin 2 ⊕ Fin 2) K ⧸ bipartiteIdeal K 2 2 ^ 3) = 132 := by
  rw [compositionLength_formula K 2 2 3 (by omega) (by omega) (by omega)]
  norm_num [correction, Finset.sum_range_succ, Finset.sum_Icc_succ_top, Nat.choose]

/-- The balanced smallest case has an empty higher-sign interval. -/
example : ∀ i ≤ 2, 0 ≤ hilbertCoefficient 1 1 i := by
  apply (release_main_theorem ℚ 1 1 (by omega) (by omega)).all_nonnegative_iff.mpr
  norm_num

/-- The difficult unequal-parity regime is included. -/
example : 0 < hilbertCoefficient 3 4 5 := by
  rw [hilbertCoefficient_eq_formula 3 4 5 (by omega) (by omega)]
  exact coefficientFormula_high_pos_of_odd 3 4 5 (by omega) (by omega)
    (by omega) (by omega) (by exact ⟨1, by omega⟩)

example : hilbertCoefficient 4 5 7 < 0 := by
  rw [hilbertCoefficient_eq_formula 4 5 7 (by omega) (by omega)]
  exact coefficientFormula_high_neg_of_even 4 5 7 (by omega) (by omega)
    (by omega) (by omega) (by exact ⟨2, by omega⟩)
