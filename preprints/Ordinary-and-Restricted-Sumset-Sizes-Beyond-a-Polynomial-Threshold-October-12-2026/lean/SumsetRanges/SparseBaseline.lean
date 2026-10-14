import SumsetRanges.LargeConstruction
import SumsetRanges.SparseBounds

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

@[simp] theorem ambiguityPolynomial_zero (m : ℕ) : ambiguityPolynomial m 0=1 := by
  simp [ambiguityPolynomial]
theorem ambiguityPolynomial_one (m : ℕ) (hm : 2≤m) : ambiguityPolynomial m 1=X+X^(m-1) := by
  have he : 1+(m-2)=m-1 := by omega
  simp [ambiguityPolynomial,sum_range_succ,he]

theorem sharedBlockPolynomial_one (m : ℕ) (hm : 2≤m) : sharedBlockPolynomial m 1=(1+X)^m := by
  rw [sharedBlockPolynomial_formula m 1 hm]
  simp only [show 1+1=2 by rfl,Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.choose_zero_right,Nat.choose_self,Nat.cast_one,Nat.sub_zero,Nat.sub_self,
    pow_one,pow_zero,ambiguityPolynomial_zero,ambiguityPolynomial_one m hm,
    one_mul,mul_one,zero_add]
  ring

theorem sparsePolynomial_baseline (h c : ℕ)
    (hn : nonfreeSize h (fun _ => 0) (fun _ => 1)≤c) :
    sparsePolynomial h c (fun _ => 0) (fun _ => 1)=(1+X)^c := by
  unfold sparsePolynomial
  have hp : (∏m∈Icc 2 h,restrictedPolynomial (linearBlocks m 0)*sharedBlockPolynomial m 1)=
      (1+X)^(nonfreeSize h (fun _ => 0) (fun _ => 1)) := by
    calc
      _=∏m∈Icc 2 h,(1+X)^m := by
        apply Finset.prod_congr rfl
        intro m hm
        rw [restrictedPolynomial_linearBlocks m 0 (mem_Icc.mp hm).1,
          sharedBlockPolynomial_one m (mem_Icc.mp hm).1]
        simp
      _=_ := by rw [Finset.prod_pow_eq_pow_sum]; simp [nonfreeSize]
  rw [hp,← pow_add,Nat.sub_add_cancel hn]

end SumsetRanges
