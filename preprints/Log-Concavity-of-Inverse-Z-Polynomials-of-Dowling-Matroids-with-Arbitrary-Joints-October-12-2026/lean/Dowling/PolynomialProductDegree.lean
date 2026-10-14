import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
namespace Dowling
open scoped Classical BigOperators

/-- Two positive-rank strict half-degree factors leave a full unit of degree
below the odd-rank top coefficient. -/
theorem polynomial_product_two_strict {ι : Type*} [Fintype ι]
    (f : ι → Polynomial ℤ) (r : ι → ℕ)
    (hle : ∀ i, 2*(f i).natDegree≤r i)
    (c d : ι) (hcd : c≠d)
    (hc : 2*(f c).natDegree<r c) (hd : 2*(f d).natDegree<r d) :
    2*(∏ i, f i).natDegree+2≤∑ i, r i := by
  have hp (i : ι) : 2*(f i).natDegree+(if i=c then 1 else 0)+(if i=d then 1 else 0)≤r i := by
    by_cases hic : i=c
    · subst i
      simp only [ite_true,hcd,ite_false,Nat.add_zero]
      omega
    · by_cases hid : i=d
      · subst i
        simp only [hic,ite_false,ite_true,Nat.add_zero]
        omega
      · simp only [hic,hid,ite_false,Nat.add_zero]
        exact hle i
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  have hdg := Polynomial.natDegree_prod_le Finset.univ f
  omega

end Dowling
