import Dowling.ReciprocalUniqueness
import Fan.CoefficientChangeVariable

noncomputable section
namespace Dowling
open PowerSeries Finset

theorem flat_transform_discrepancy {R : Type*} [CommRing R]
    (E U P Q : PowerSeries R) (hE : E.constantCoeff=1) (hU : U.constantCoeff=1)
    (n : ℕ) (hPQ : ∀ k, k<n → coeff k P=coeff k Q) :
    coeff n (E*P.subst (X*U))-coeff n (E*Q.subst (X*U)) = coeff n P-coeff n Q := by
  rw [mul_comm E,mul_comm E, Fan.coeff_subst_X_mul_product,Fan.coeff_subst_X_mul_product,
    ← sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [sum_eq_single n]
  · simp only [Nat.sub_self,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,hU,hE,
      one_pow,mul_one]
  · intro k hk hkn
    rw [hPQ k (by have := mem_range.mp hk; omega),sub_self,zero_mul]
  · intro hn
    exact False.elim (hn (mem_range.mpr (Nat.lt_succ_self n)))

/-- Strict-half KL support and reciprocal Z rows uniquely determine any
unit-linear flat transform, including the full Dowling transform. -/
theorem flat_transform_unique
    (E U P Z P' Z' : PowerSeries (Polynomial ℝ))
    (hE : E.constantCoeff=1) (hU : U.constantCoeff=1)
    (h0 : coeff 0 P=coeff 0 P')
    (hP : ∀ n, 0<n → ∀ k, n≤2*k → (coeff n P).coeff k=0)
    (hP' : ∀ n, 0<n → ∀ k, n≤2*k → (coeff n P').coeff k=0)
    (hZ : ∀ n t, t≠0 → t^n*(coeff n Z).eval t⁻¹=(coeff n Z).eval t)
    (hZ' : ∀ n t, t≠0 → t^n*(coeff n Z').eval t⁻¹=(coeff n Z').eval t)
    (he : Z=E*P.subst (X*U)) (he' : Z'=E*P'.subst (X*U)) : P=P' ∧ Z=Z' := by
  have hall : ∀ n, coeff n P=coeff n P' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n=0
      · subst n; exact h0
      have hn0 : 0<n := Nat.pos_of_ne_zero hn
      have hd : coeff n Z-coeff n Z'=coeff n P-coeff n P' := by
        rw [he,he']
        exact flat_transform_discrepancy E U P P' hE hU n ih
      apply sub_eq_zero.mp
      apply low_support_reciprocal_zero _ n
      · intro k hk
        simp only [Polynomial.coeff_sub,hP n hn0 k hk,hP' n hn0 k hk,sub_self]
      · intro t ht
        rw [← hd,Polynomial.eval_sub,Polynomial.eval_sub,mul_sub,hZ n t ht,hZ' n t ht]
  have hp : P=P' := PowerSeries.ext hall
  exact ⟨hp,by rw [he,he',hp]⟩

end Dowling
