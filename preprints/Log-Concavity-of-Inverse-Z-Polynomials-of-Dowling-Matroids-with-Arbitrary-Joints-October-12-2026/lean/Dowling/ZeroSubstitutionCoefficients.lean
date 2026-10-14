import Fan.CoefficientChangeVariable

noncomputable section
namespace Dowling
open scoped BigOperators
open PowerSeries
variable {R : Type*} [CommRing R]

/-- Finite coefficient expansion for a zero-constant substitution, with an
arbitrary prefactor. All omitted powers vanish for degree reasons. -/
theorem coeff_mul_subst_zero (A Y B : PowerSeries R) (hB : B.constantCoeff=0) (n : ℕ) :
    coeff n (A*Y.subst B)=∑ k ∈ Finset.range (n+1), coeff k Y*coeff n (A*B^k) := by
  let u := PowerSeries.mk (fun j => coeff (j+1) B)
  have he : B=X*u := by
    simpa only [hB,map_zero,add_zero] using eq_X_mul_shift_add_const B
  rw [mul_comm,he,Fan.coeff_subst_X_mul_product]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k≤n := by simpa using Finset.mem_range.mp hk
  rw [mul_pow,show A*(X^k*u^k)=X^k*(u^k*A) by ring,coeff_X_pow_mul',ite_eq_left hkn]

theorem coeff_mul_neg_pow (A B : PowerSeries R) (n k : ℕ) :
    coeff n (A*(-B)^k)=(-1:R)^k*coeff n (A*B^k) := by
  have he : A*(-B)^k=C ((-1:R)^k)*(A*B^k) := by
    rw [map_pow,map_neg,map_one,neg_pow B k]
    ring
  rw [he,coeff_C_mul]

end Dowling
