import Dowling.WhitneySeriesEvaluation
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
namespace Dowling
open Polynomial

theorem eval_reflect_nonzero (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (t : ℝ) (ht : t ≠ 0) : (reflect n p).eval t = t^n*p.eval t⁻¹ := by
  let : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht)
  have h := eval₂_reflect_mul_pow (RingHom.id ℝ) (t⁻¹) n p hp
  simp only [eval₂_id,invOf_eq_inv,inv_inv] at h
  calc
    (reflect n p).eval t = ((reflect n p).eval t*(t⁻¹)^n)*t^n := by
      rw [mul_assoc,← mul_pow,inv_mul_cancel₀ ht,one_pow,mul_one]
    _ = _ := by rw [h]; ring

theorem polynomial_eq_of_eval_nonzero (p q : Polynomial ℝ)
    (h : ∀ t : ℝ, t ≠ 0 → p.eval t = q.eval t) : p=q := by
  have he : X*(p-q)=0 := by
    apply Polynomial.funext
    intro t
    by_cases ht : t=0
    · simp [ht]
    · simp only [eval_mul,eval_X,eval_sub,eval_zero,h t ht,sub_self,mul_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left X_ne_zero)

/-- Pointwise reciprocity already forces a strict lower-half polynomial to vanish. -/
theorem low_support_reciprocal_zero (p : Polynomial ℝ) (n : ℕ)
    (hlow : ∀ j, n ≤ 2*j → p.coeff j = 0)
    (hrec : ∀ t : ℝ, t ≠ 0 → t^n*p.eval t⁻¹=p.eval t) : p=0 := by
  have hd : p.natDegree ≤ n := (natDegree_le_iff_coeff_eq_zero).mpr (fun j hj => hlow j (by omega))
  have hr : reflect n p = p := polynomial_eq_of_eval_nonzero _ _ (fun t ht => by
    rw [eval_reflect_nonzero p n hd t ht,hrec t ht])
  ext j
  rw [coeff_zero]
  by_cases hj : n ≤ 2*j
  · exact hlow j hj
  · have hjn : j ≤ n := by omega
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff j) hr
    rw [coeff_reflect,revAt_le hjn,hlow (n-j) (by omega)] at hc
    exact hc.symm

end Dowling
