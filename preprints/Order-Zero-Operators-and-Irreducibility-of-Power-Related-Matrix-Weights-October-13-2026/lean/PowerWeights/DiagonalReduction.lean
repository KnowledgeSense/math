import PowerWeights.LowerElimination

namespace PowerWeights

open Polynomial

variable {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (ha : ∀ i, i+1<N → a i≠0) (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F))
include ha h

 theorem upper_block_relations (i j : Fin N) (hi : i.val%2=0) (hj : j.val%2=1) :
    F i j=0 ∧ (F*pathMatrix N a-pathMatrix N a*F) i j=0 := by
  have he := transformed_entry_relation s a F h i j
  have hlo := lower_block_zero s a ha F h j i hj hi
  rw [lower_transformed_constant a F j i hj hi, hlo] at he
  have hG : transformed a F i j=0 := by
    have he' : transformed a F i j*X^exponent s j.val=0 := by simpa [conjugate] using he
    exact (mul_eq_zero.mp he').resolve_right (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [transformed_linear s a F h] at hG
  have h₀ := congrArg (fun p : ℂ[X] => p.coeff 0) hG
  have h₁ := congrArg (fun p : ℂ[X] => p.coeff 1) hG
  constructor
  · simpa [coeff_C_mul_X] using h₀
  · simpa [coeff_C_mul_X] using h₁

 theorem same_parity_commutator (i j : Fin N) (hp : i.val%2=j.val%2) :
    (F*pathMatrix N a-pathMatrix N a*F) i j=0 := by
  by_cases hj : j.val%2=0
  · have hi : i.val%2=0 := by omega
    have hFA := mul_path_even_column a F i j hj
    have hAF : (pathMatrix N a*F) i j=0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro t _
      by_cases hat : pathMatrix N a i t=0
      · simp [hat]
      have ht := (path_support hat).2.1
      simp [lower_block_zero s a ha F h t j ht hj]
    simp [Matrix.sub_apply,hFA,hAF]
  · have hi : i.val%2=1 := by omega
    have hAF := path_mul_odd_row a F i j hi
    have hFA := lower_times_path_zero s a ha F h i j hi
    simp [Matrix.sub_apply,hFA,hAF]

 theorem same_parity_transformed (i j : Fin N) (hp : i.val%2=j.val%2) :
    transformed a F i j=C (F i j) := by
  rw [transformed_linear s a F h, same_parity_commutator s a ha F h i j hp]
  simp

 theorem off_diagonal_zero (i j : Fin N) (hne : i≠j) : F i j=0 := by
  by_cases hp : i.val%2=j.val%2
  · have he := transformed_entry_relation s a F h i j
    rw [same_parity_transformed s a ha F h i j hp,
      same_parity_transformed s a ha F h j i hp.symm, conjugate_C] at he
    have hex : exponent s j.val ≠ exponent s i.val := by
      intro hh
      apply hne
      apply Fin.ext
      exact exponent_injective_on_parity s i.val j.val hp hh.symm
    exact (monomial_coefficients_zero _ _ _ _ hex he).1
  · by_cases hi : i.val%2=0
    · have hj : j.val%2=1 := by omega
      exact (upper_block_relations s a ha F h i j hi hj).1
    · have hi' : i.val%2=1 := by omega
      have hj : j.val%2=0 := by omega
      exact lower_block_zero s a ha F h i j hi' hj

 theorem diagonal_star_fixed (i : Fin N) : star (F i i)=F i i := by
  have he := transformed_entry_relation s a F h i i
  rw [same_parity_transformed s a ha F h i i rfl, conjugate_C] at he
  have hc := congrArg (fun p : ℂ[X] => p.coeff (exponent s i.val)) he
  simpa [coeff_C_mul_X_pow] using hc.symm

 theorem diagonal_form : F=Matrix.diagonal (fun i => F i i) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp
  · simp [Matrix.diagonal, hij, off_diagonal_zero s a ha F h i j hij]

 theorem commutes_path : F*pathMatrix N a=pathMatrix N a*F := by
  ext i j
  by_cases hp : i.val%2=j.val%2
  · exact sub_eq_zero.mp (same_parity_commutator s a ha F h i j hp)
  · by_cases hi : i.val%2=0
    · have hj : j.val%2=1 := by omega
      exact sub_eq_zero.mp (upper_block_relations s a ha F h i j hi hj).2
    · have hi' : i.val%2=1 := by omega
      have hj : j.val%2=0 := by omega
      rw [mul_path_even_column a F i j hj, path_mul_odd_row a F i j hi']

end PowerWeights
