import PowerWeights.Definitions

namespace PowerWeights

open Polynomial

/-- Entry of the conjugated degree-two polynomial matrix. -/
noncomputable def quadratic (u v w : ℂ) : ℂ[X] := C u + C v * X + C w * X^2

 theorem quadratic_monomial_support (u v w c : ℂ) (e o : ℕ)
    (hc : c ≠ 0) (h : quadratic u v w * X^e = C c * X^o) :
    o=e ∨ o=e+1 ∨ o=e+2 := by
  by_contra hn
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff o) h
  simp only [coeff_mul_X_pow', quadratic, coeff_add, coeff_C,
    coeff_C_mul_X] at hcoeff
  split_ifs at hcoeff <;> simp_all <;> omega

 theorem quadratic_top_zero (u v w c : ℂ) (e o : ℕ)
    (hne : o ≠ e+2) (h : quadratic u v w * X^e = C c * X^o) : w=0 := by
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (2+e)) h
  rw [coeff_mul_X_pow] at hcoeff
  simpa [quadratic, coeff_C_mul_X_pow, coeff_C_mul_X, Nat.add_comm,
    Ne.symm hne] using hcoeff

 theorem monomial_coefficients_zero (u v : ℂ) (e o : ℕ)
    (hne : e ≠ o) (h : C u * X^e = C v * X^o) : u=0 ∧ v=0 := by
  have he := congrArg (fun p : ℂ[X] => p.coeff e) h
  have ho := congrArg (fun p : ℂ[X] => p.coeff o) h
  constructor
  · simpa [coeff_C_mul_X_pow, hne] using he
  · simpa [coeff_C_mul_X_pow, Ne.symm hne] using ho.symm

 theorem opposite_exponent_support (s : Schedule) (i j : ℕ)
    (hi : i%2=1) (hj : j%2=0)
    (h : exponent s j = exponent s i ∨
      exponent s j = exponent s i+1 ∨ exponent s j = exponent s i+2) :
    j=i+1 ∨ (s=.printed ∧ i=1 ∧ j=0) := by
  cases s <;> simp_all [exponent] <;> omega

 theorem opposite_exponent_not_two (s : Schedule) (i j : ℕ)
    (hi : i%2=1) (hj : j%2=0) : exponent s j ≠ exponent s i+2 := by
  cases s <;> simp only [exponent] <;> omega

 theorem exponent_injective_on_parity (s : Schedule) (i j : ℕ)
    (hp : i%2=j%2) (he : exponent s i = exponent s j) : i=j := by
  cases s <;> simp only [exponent] at he <;> omega

end PowerWeights
