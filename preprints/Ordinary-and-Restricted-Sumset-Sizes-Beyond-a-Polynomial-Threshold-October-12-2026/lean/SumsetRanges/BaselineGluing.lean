import SumsetRanges.BaselineInterval

open Finset Polynomial
namespace SumsetRanges
open scoped Classical

theorem baseline_adjacent (h c b : ℕ) (hb : 3≤b) :
    baselineValue h c b (denseMaximum h b)=baselineValue h (c+1) (b-1) (b-2) := by
  unfold baselineValue denseMaximum
  have he : b-1-1=b-2 := by omega
  rw [← he,dense_endpoint_product h c (b-1) (by omega)]
  rw [he,denseSet_at_minimum]
  rw [show b-2+1=b-1 by omega]

theorem baseline_top (h k : ℕ) (hk : 2≤k) :
    baselineValue h (k-2) 2 (denseMaximum h 2)=(k.choose h : ℤ) := by
  simp only [baselineValue,denseMaximum,Nat.sub_self,Nat.mul_zero,zero_add]
  norm_num
  rw [restrictedPolynomial_pair,← pow_add,Nat.sub_add_cancel hk,
    coeff_one_add_X_pow]

end SumsetRanges
