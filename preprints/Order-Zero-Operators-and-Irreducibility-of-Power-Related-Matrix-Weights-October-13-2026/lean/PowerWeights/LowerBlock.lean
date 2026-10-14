import PowerWeights.Conjugation

namespace PowerWeights

open Polynomial

 theorem path_odd_row {N : ℕ} (a : ℕ → ℝ) (i j : Fin N)
    (hi : i.val%2=1) : pathMatrix N a i j = 0 := by
  by_contra h
  have := (path_support h).1
  omega

 theorem path_even_column {N : ℕ} (a : ℕ → ℝ) (i j : Fin N)
    (hj : j.val%2=0) : pathMatrix N a i j = 0 := by
  by_contra h
  have := (path_support h).2.1
  omega

 theorem path_mul_odd_row {N : ℕ} (a : ℕ → ℝ)
    (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (hi : i.val%2=1) :
    (pathMatrix N a*M) i j=0 := by
  simp [Matrix.mul_apply, path_odd_row a i _ hi]

 theorem mul_path_even_column {N : ℕ} (a : ℕ → ℝ)
    (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (hj : j.val%2=0) :
    (M*pathMatrix N a) i j=0 := by
  simp [Matrix.mul_apply, path_even_column a _ j hj]

 theorem lower_transformed_constant {N : ℕ} (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    (hi : i.val%2=1) (hj : j.val%2=0) :
    transformed a F i j = C (F i j) := by
  rw [transformed_entry]
  simp [Matrix.sub_apply, mul_path_even_column a F i j hj,
    path_mul_odd_row a F i j hi, mul_path_even_column a (pathMatrix N a*F) i j hj,
    quadratic]

 theorem lower_entry_support {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F)) (i j : Fin N)
    (hi : i.val%2=1) (hj : j.val%2=0) (hf : F i j ≠ 0) :
    j.val=i.val+1 ∨ (s=.printed ∧ i.val=1 ∧ j.val=0) := by
  have he := transformed_entry_relation s a F h j i
  rw [lower_transformed_constant a F i j hi hj, conjugate_C,
    transformed_entry] at he
  have hc : star (F i j) ≠ 0 := by simpa using hf
  exact opposite_exponent_support s i.val j.val hi hj
    (quadratic_monomial_support _ _ _ _ _ _ hc he)

 theorem path_sandwich_zero {N : ℕ} (s : Schedule) (a : ℕ → ℝ)
    (F : Matrix (Fin N) (Fin N) ℂ)
    (h : constant F * polynomialWeight N s a =
      polynomialWeight N s a * adjoint (constant F)) :
    pathMatrix N a*F*pathMatrix N a = 0 := by
  ext i j
  by_cases hi : i.val%2=1
  · rw [mul_assoc, path_mul_odd_row a (F*pathMatrix N a) i j hi]
    rfl
  by_cases hj : j.val%2=0
  · exact mul_path_even_column a (pathMatrix N a*F) i j hj
  have hi' : i.val%2=0 := by omega
  have hj' : j.val%2=1 := by omega
  have he := transformed_entry_relation s a F h i j
  rw [lower_transformed_constant a F j i hj' hi', conjugate_C,
    transformed_entry] at he
  have hz := quadratic_top_zero _ _ _ _ _ _
    (opposite_exponent_not_two s j.val i.val hj' hi') he
  simpa using hz

end PowerWeights
