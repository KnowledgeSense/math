import OscillatoryRecurrence.Orthogonality

noncomputable section
open scoped BigOperators
open Polynomial
namespace OscillatoryRecurrence

 def recurrenceDiagonal (η : ℝ) (n : ℕ) : ℂ :=
  (orthogonalPolynomial η (n+1)).coeff n -
    (orthogonalPolynomial η (n+2)).coeff (n+1)

 def recurrenceLower (η : ℝ) (n : ℕ) : ℂ :=
  squaredNorm η (n+1) / squaredNorm η n

 theorem recurrence_remainder_degree (η : ℝ) (n : ℕ) :
    (X*orthogonalPolynomial η (n+1) - orthogonalPolynomial η (n+2) -
      C (recurrenceDiagonal η n)*orthogonalPolynomial η (n+1) -
      C (recurrenceLower η n)*orthogonalPolynomial η n).degree < ((n+1 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
  simp only [Nat.succ_eq_add_one, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
  have hz (a b : ℕ) (h : a<b) : (orthogonalPolynomial η a).coeff b = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [orthogonalPolynomial_natDegree]; exact h)
  rcases eq_or_lt_of_le (show n≤k by omega) with hk | hk
  · subst k
    rw [orthogonalPolynomial_coeff_leading η (n+1), hz n (n+1) (by omega)]
    unfold recurrenceDiagonal
    ring
  · rcases eq_or_lt_of_le (show n+1≤k by omega) with hk' | hk'
    · subst k
      rw [orthogonalPolynomial_coeff_leading η (n+1),
        orthogonalPolynomial_coeff_leading η (n+2),
        hz (n+1) (n+1+1) (by omega), hz n (n+1+1) (by omega)]
      ring
    · rw [hz (n+1) k hk', hz (n+2) (k+1) (by omega),
        hz (n+1) (k+1) (by omega), hz n (k+1) (by omega)]
      ring

 theorem momentFunctional_C_mul (η : ℝ) (k : ℕ) (c : ℂ) (p : ℂ[X]) :
    momentFunctional η k (C c*p) = c*momentFunctional η k p := by
  rw [← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]

/-- Three-term recurrence for the monic polynomials of the original bilinear weight. -/
 theorem three_term_recurrence (m : ℤ) (hm : m ≠ 0) (n : ℕ) :
    X*orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1) =
      orthogonalPolynomial ((m:ℝ)*Real.pi) (n+2) +
      C (recurrenceDiagonal ((m:ℝ)*Real.pi) n)*orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1) +
      C (recurrenceLower ((m:ℝ)*Real.pi) n)*orthogonalPolynomial ((m:ℝ)*Real.pi) n := by
  have hz := zero_of_moments_zero m hm (n+1) _ (recurrence_remainder_degree ((m:ℝ)*Real.pi) n) ?_
  · linear_combination hz
  intro k
  simp only [map_sub,momentFunctional_C_mul]
  have hshift := momentFunctional_shift ((m:ℝ)*Real.pi) k.val 1
    (orthogonalPolynomial ((m:ℝ)*Real.pi) (n+1))
  rw [pow_one] at hshift
  rw [hshift,orthogonalPolynomial_orthogonal m hm (n+2) k.val (by omega),
    orthogonalPolynomial_orthogonal m hm (n+1) k.val k.is_lt,mul_zero,sub_zero,sub_zero]
  rcases lt_or_eq_of_le (show k.val≤n by omega) with hk | hk
  · rw [orthogonalPolynomial_orthogonal m hm (n+1) (k.val+1) (by omega),
      orthogonalPolynomial_orthogonal m hm n k.val hk,mul_zero,sub_self]
  · rw [hk]
    change squaredNorm ((m:ℝ)*Real.pi) (n+1) -
      (squaredNorm ((m:ℝ)*Real.pi) (n+1) / squaredNorm ((m:ℝ)*Real.pi) n)*
        squaredNorm ((m:ℝ)*Real.pi) n = 0
    rw [div_mul_cancel₀ _ (squaredNorm_ne_zero m hm n),sub_self]

end OscillatoryRecurrence
