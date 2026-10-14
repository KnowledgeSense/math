import BoseBurton.ZIncidenceConvolution

noncomputable section
namespace BoseBurton
open Polynomial

theorem strict_half_reflect_eq_zero (d : ℕ) (p : Polynomial ℤ)
    (hlow : ∀ i,d≤2*i→p.coeff i=0) (hpal : reflect d p=p) : p=0 := by
  ext i
  simp only [coeff_zero]
  by_cases hi : d≤2*i
  · exact hlow i hi
  · have h := congrArg (fun q : Polynomial ℤ=>q.coeff i) hpal
    rw [coeff_reflect,revAt_le (by omega),hlow (d-i) (by omega)] at h
    exact h.symm

theorem strict_half_palindromic_difference (d : ℕ) (hd : 0<d)
    (p : Polynomial ℤ) (hlow : ∀ i,d≤2*i→p.coeff i=0)
    (hpal : reflect d (p-1)=p-1) : p=1 := by
  apply sub_eq_zero.mp
  apply strict_half_reflect_eq_zero d (p-1) _ hpal
  intro i hi
  rw [coeff_sub,hlow i hi,coeff_one]
  have h : i≠0 := by omega
  simp [h]

end BoseBurton
