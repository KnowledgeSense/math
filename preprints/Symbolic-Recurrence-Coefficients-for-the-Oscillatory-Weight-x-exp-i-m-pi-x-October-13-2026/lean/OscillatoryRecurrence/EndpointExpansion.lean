import OscillatoryRecurrence.PolynomialMoments
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
open Polynomial Finset
open scoped BigOperators
namespace OscillatoryRecurrence

/-- Integration of monomials against the exponential density, at a shifted order. -/
def factorialTransform (u : ℕ) (p : ℚ[X]) : ℚ[X] :=
  p.sum (fun j a => monomial j (a*(j+u).factorial))

 theorem factorialTransform_coeff (u : ℕ) (p : ℚ[X]) (j : ℕ) :
    (factorialTransform u p).coeff j=p.coeff j*(j+u).factorial := by
  classical
  simp only [factorialTransform,Polynomial.sum,finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · intro hj
    simp [notMem_support_iff.mp hj]

 theorem factorialTransform_X_pow_mul (u : ℕ) (p : ℚ[X]) :
    factorialTransform 0 (X^u*p)=X^u*factorialTransform u p := by
  ext j
  by_cases hj : u≤j
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm u k,coeff_X_pow_mul,factorialTransform_coeff,
      coeff_X_pow_mul,factorialTransform_coeff]
    simp
  · simp [factorialTransform_coeff,coeff_X_pow_mul',hj]

 theorem factorialTransform_add (u : ℕ) (p q : ℚ[X]) :
    factorialTransform u (p+q)=factorialTransform u p+factorialTransform u q := by
  ext j
  simp only [factorialTransform_coeff,coeff_add]
  ring

 theorem factorialTransform_C_mul (u : ℕ) (a : ℚ) (p : ℚ[X]) :
    factorialTransform u (C a*p)=C a*factorialTransform u p := by
  ext j
  simp only [factorialTransform_coeff,coeff_C_mul]
  ring

 theorem factorialTransform_neg (u : ℕ) (p : ℚ[X]) :
    factorialTransform u (-p) = -factorialTransform u p := by
  ext j
  simp [factorialTransform_coeff]

 theorem factorialTransform_derivative (p : ℚ[X]) :
    factorialTransform 0 p=C (p.eval 0)+X*factorialTransform 0 p.derivative := by
  ext j
  cases j with
  | zero =>
    rw [factorialTransform_coeff]
    simp [← coeff_zero_eq_eval_zero]
  | succ j =>
    rw [coeff_add,coeff_C,ite_eq_right (by omega),zero_add,coeff_X_mul,
      factorialTransform_coeff,factorialTransform_coeff,coeff_derivative]
    simp [Nat.factorial_succ]
    ring

/-- The exact endpoint polynomial after removal of the common exponential factor. -/
def endpointExpansion (p : ℚ[X]) : ℚ[X] :=
  X*(factorialTransform 0 (p.comp (C 1-X))-
    factorialTransform 0 (p.comp (C (-1)-X)))

 theorem endpointExpansion_add (p q : ℚ[X]) :
    endpointExpansion (p+q)=endpointExpansion p+endpointExpansion q := by
  simp only [endpointExpansion,add_comp,factorialTransform_add]
  ring

 theorem endpointExpansion_C_mul (a : ℚ) (p : ℚ[X]) :
    endpointExpansion (C a*p)=C a*endpointExpansion p := by
  simp only [endpointExpansion,mul_comp,C_comp,factorialTransform_C_mul]
  ring

 theorem endpointExpansion_derivative (p : ℚ[X]) :
    endpointExpansion p=X*C (p.eval 1-p.eval (-1))-X*endpointExpansion p.derivative := by
  have hp := factorialTransform_derivative (p.comp (C 1-X))
  have hm := factorialTransform_derivative (p.comp (C (-1)-X))
  simp only [eval_comp,eval_sub,eval_C,eval_X,sub_zero,derivative_comp,
    derivative_sub,derivative_C,derivative_X,zero_sub,neg_one_mul,
    factorialTransform_neg] at hp hm
  unfold endpointExpansion
  rw [hp,hm,C_sub]
  ring

@[simp] theorem endpointExpansion_one : endpointExpansion (1:ℚ[X])=0 := by
  simp [endpointExpansion]

 theorem endpointExpansion_X_pow_succ (r : ℕ) :
    endpointExpansion (X^(r+1))=X*C (1-(-1:ℚ)^(r+1))-
      C ((r:ℚ)+1)*X*endpointExpansion (X^r) := by
  rw [endpointExpansion_derivative]
  simp only [eval_pow,eval_X,one_pow,derivative_X_pow,Nat.add_sub_cancel,
    endpointExpansion_C_mul,Nat.cast_add,Nat.cast_one]
  ring

 theorem endpointExpansion_exponentialMoment (t s : ℂ) (ht : t≠0)
    (hplus : Complex.exp t=s) (hminus : Complex.exp (-t)=s) (r : ℕ) :
    s*(endpointExpansion (X^r)).eval₂ (Rat.castHom ℂ) t⁻¹=exponentialMoment t r := by
  induction r with
  | zero => simp [exponentialMoment_zero t ht,hplus,hminus]
  | succ r ih =>
    rw [endpointExpansion_X_pow_succ]
    simp only [eval₂_sub,eval₂_mul,eval₂_X]
    simp
    have h := exponentialMoment_recurrence t r
    rw [hplus,hminus] at h
    apply (mul_left_cancel₀ ht)
    have hi := congrArg (fun z : ℂ => ((r:ℂ)+1)*z) ih
    field_simp
    simp only [one_div] at *
    simp only [eval₂_pow,eval₂_neg,eval₂_one]
    linear_combination -h-hi

def endpointTail (ε : ℚ) (u d : ℕ) : ℚ[X] :=
  (X-C (2*ε))^u*(C ε-X)^d

 theorem endpoint_factorization (ε : ℚ) (hε : ε^2=1) (u d : ℕ) :
    (((X^2-1)^u*X^d : ℚ[X]).comp (C ε-X))=X^u*endpointTail ε u d := by
  simp only [mul_comp,pow_comp,sub_comp,X_comp,one_comp]
  have h : (C ε-X)^2-1=(X:ℚ[X])*(X-C (2*ε)) := by
    have hc : (C ε : ℚ[X])^2=1 := by rw [← C_pow,hε,C_1]
    rw [C_mul,C_ofNat]
    linear_combination hc
  rw [h,mul_pow]
  simp only [endpointTail]
  ring

 theorem endpointExpansion_factor (u d : ℕ) :
    endpointExpansion ((X^2-1)^u*X^d)=X^(u+1)*
      (factorialTransform u (endpointTail 1 u d)-
       factorialTransform u (endpointTail (-1) u d)) := by
  unfold endpointExpansion
  rw [endpoint_factorization 1 (by norm_num),endpoint_factorization (-1) (by norm_num),
    factorialTransform_X_pow_mul,factorialTransform_X_pow_mul]
  ring

 theorem endpointTail_coeff_zero (ε : ℚ) (u d : ℕ) :
    (endpointTail ε u d).coeff 0=(-2*ε)^u*ε^d := by
  rw [coeff_zero_eq_eval_zero]
  simp [endpointTail]

 theorem endpointExpansion_leading (u d : ℕ) :
    (endpointExpansion ((X^2-1)^u*X^d)).coeff (u+1)=
      (u.factorial:ℚ)*((-2)^u-2^u*(-1)^d) := by
  rw [endpointExpansion_factor]
  have h := coeff_X_pow_mul
    (factorialTransform u (endpointTail 1 u d)-factorialTransform u (endpointTail (-1) u d))
    (u+1) 0
  simp only [zero_add] at h
  rw [h,coeff_sub,factorialTransform_coeff,factorialTransform_coeff,
    endpointTail_coeff_zero,endpointTail_coeff_zero]
  simp
  ring

 theorem coeff_one_eq_eval_derivative (p : ℚ[X]) :
    p.coeff 1=p.derivative.eval 0 := by
  rw [← coeff_zero_eq_eval_zero,coeff_derivative]
  simp

 theorem endpointTail_one_coeff_one (u d : ℕ) :
    (endpointTail 1 u d).coeff 1=(-2:ℚ)^u*(-(d:ℚ)-(u:ℚ)/2) := by
  rw [coeff_one_eq_eval_derivative]
  simp only [endpointTail,derivative_mul,derivative_pow,derivative_sub,
    derivative_X,derivative_C,sub_zero,zero_sub,eval_add,eval_mul,eval_C,
    eval_pow,eval_sub,eval_X,eval_neg,eval_one]
  cases u <;> cases d <;> simp [pow_succ] <;> ring

 theorem endpointTail_neg_one_coeff_one (u d : ℕ) :
    (endpointTail (-1) u d).coeff 1=(2:ℚ)^u*(-1)^d*((d:ℚ)+(u:ℚ)/2) := by
  rw [coeff_one_eq_eval_derivative]
  simp only [endpointTail,derivative_mul,derivative_pow,derivative_sub,
    derivative_X,derivative_C,sub_zero,zero_sub,eval_add,eval_mul,eval_C,
    eval_pow,eval_sub,eval_X,eval_neg,eval_one]
  cases u <;> cases d <;> simp [pow_succ] <;> ring

 theorem endpointExpansion_next (u d : ℕ) :
    (endpointExpansion ((X^2-1)^u*X^d)).coeff (u+2)=
      -((u+1).factorial:ℚ)*((d:ℚ)+(u:ℚ)/2)*((-2)^u+2^u*(-1)^d) := by
  rw [endpointExpansion_factor,show u+2=1+(u+1) by omega,coeff_X_pow_mul,
    coeff_sub,factorialTransform_coeff,factorialTransform_coeff,
    endpointTail_one_coeff_one,endpointTail_neg_one_coeff_one]
  rw [Nat.add_comm 1 u]
  ring

end OscillatoryRecurrence
