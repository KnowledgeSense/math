import Dowling.DeletionIncidenceLift

noncomputable section
namespace Dowling
open Finset LaurentPolynomial

theorem deletionLift_finset_sum {ι : Type*} (d : ℤ) (s : Finset ι) (p : ι→Polynomial ℤ) :
    deletionLift d (∑ i ∈ s,p i)=∑ i ∈ s,deletionLift d (p i) := by
  simp only [deletionLift,map_sum,mul_sum]

/-- Literal Laurent inversion corresponds to rank reflection on bounded polynomials. -/
theorem deletionLift_invert (d : ℕ) (p : Polynomial ℤ)
    (hp : p.natDegree≤d) :
    invert (deletionLift d p)=deletionLift d (Polynomial.reflect d p) := by
  have he : Polynomial.reflect d p=∑ k ∈ p.support,
      Polynomial.monomial (d-k) (p.coeff k) := by
    conv_lhs => rw [Polynomial.as_sum_support p]
    rw [MatroidInverseZ.reflect_finset_sum]
    apply sum_congr rfl
    intro k hk
    rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.reflect_C_mul_X_pow,
      Polynomial.revAt_le ((Polynomial.le_natDegree_of_mem_supp k hk).trans hp),
      Polynomial.C_mul_X_pow_eq_monomial]
  rw [deletionLift_as_sum,map_sum,he,deletionLift_finset_sum]
  apply sum_congr rfl
  intro k hk
  rw [map_mul,invert_C,invert_T,deletionLift_monomial]
  congr 2
  have hkd := (Polynomial.le_natDegree_of_mem_supp k hk).trans hp
  omega

theorem deletionLift_palindromic (d : ℕ) (p : Polynomial ℤ)
    (hp : p.natDegree≤d) (hs : Polynomial.reflect d p=p) :
    invert (deletionLift d p)=deletionLift d p := by
  rw [deletionLift_invert d p hp,hs]

end Dowling
