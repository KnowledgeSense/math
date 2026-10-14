import Dowling.DeletionIncidencePerverse

noncomputable section
namespace Dowling
open Finset LaurentPolynomial

 theorem deletionLift_as_sum (d : ℤ) (p : Polynomial ℤ) :
    deletionLift d p=∑ k ∈ p.support,C (p.coeff k)*T (d-2*k) := by
  conv_lhs => rw [Polynomial.as_sum_support p]
  simp only [deletionLift,map_sum,mul_sum]
  apply sum_congr rfl
  intro k hk
  exact deletionLift_monomial d k (p.coeff k)

 theorem deletionLift_coeff (d : ℤ) (p : Polynomial ℤ) (j : ℤ) :
    (deletionLift d p).coeff j=∑ k ∈ p.support,if d-2*(k : ℤ)=j then p.coeff k else 0 := by
  rw [deletionLift_as_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply sum_congr rfl
  intro k hk
  exact deletionLaurent_monomial_coeff _ _ _

 theorem deletionLift_polynomial (d : ℤ) (p : Polynomial ℤ)
    (hp : ∀ k,p.coeff k≠0 → 0≤d-2*(k : ℤ)) :
    ∃ q : Polynomial ℤ,deletionLift d p=q.toLaurent := by
  refine ⟨∑ k ∈ p.support,Polynomial.monomial (d-2*(k : ℤ)).toNat (p.coeff k),?_⟩
  rw [deletionLift_as_sum,map_sum]
  apply sum_congr rfl
  intro k hk
  rw [Polynomial.toLaurent_C_mul_T,Int.toNat_of_nonneg (hp k (Polynomial.mem_support_iff.mp hk))]

 theorem deletionLift_coeff_zero (d : ℤ) (p : Polynomial ℤ)
    (hp : ∀ k,p.coeff k≠0 → 0<d-2*(k : ℤ)) : (deletionLift d p).coeff 0=0 := by
  rw [deletionLift_coeff]
  apply sum_eq_zero
  intro k hk
  rw [ite_eq_right (ne_of_gt (hp k (Polynomial.mem_support_iff.mp hk)))]

 theorem deletionSubst_coeff (p : Polynomial ℤ) (n : ℕ) :
    (deletionSubst p).coeff (-2*(n : ℤ))=p.coeff n := by
  have h := deletionLift_coeff 0 p (-2*(n : ℤ))
  simp only [deletionLift,T_zero,one_mul,zero_sub] at h
  rw [h,sum_eq_single n]
  · rw [ite_eq_left (by omega)]
  · intro k hk hkn
    rw [ite_eq_right (by omega)]
  · intro hn
    have hc : p.coeff n=0 := Polynomial.notMem_support_iff.mp hn
    simp [hc]

 theorem deletionSubst_injective : Function.Injective deletionSubst := by
  intro p q h
  ext n
  have hc := congrArg (fun f : DeletionLaurent=>f.coeff (-2*(n : ℤ))) h
  simpa only [deletionSubst_coeff] using hc

end Dowling
