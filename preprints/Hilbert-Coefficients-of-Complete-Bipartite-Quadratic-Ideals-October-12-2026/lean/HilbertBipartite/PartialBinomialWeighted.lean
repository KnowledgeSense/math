import HilbertBipartite.PartialBinomial

open Finset

namespace HilbertBipartite

theorem partialBinomial_choose_weight (M N c : ℕ) (x : ℚ) (hc : c ≤ M) :
    (∑ j ∈ range (M + 1), x ^ j * (N.choose j : ℚ) * (j.choose c : ℚ)) =
      x ^ c * (N.choose c : ℚ) * partialBinomial (M-c) (N-c) x := by
  rw [show M+1=c+(M-c+1) by omega, sum_range_add]
  have hz : (∑ j ∈ range c, x ^ j * (N.choose j : ℚ) * (j.choose c : ℚ)) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
    simp
  rw [hz, zero_add]
  unfold partialBinomial
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  have h : (N.choose (c+j) : ℚ) * ((c+j).choose c : ℚ) =
      (N.choose c : ℚ) * ((N-c).choose j : ℚ) := by
    have hh := Nat.choose_mul (n:=N) (k:=c+j) (s:=c) (by omega)
    rw [Nat.add_sub_cancel_left] at hh
    exact_mod_cast hh
  rw [pow_add]
  calc
    x^c*x^j*(N.choose (c+j):ℚ)*((c+j).choose c:ℚ) =
        x^c*x^j*((N.choose (c+j):ℚ)*((c+j).choose c:ℚ)) := by ring
    _ = x^c*x^j*((N.choose c:ℚ)*((N-c).choose j:ℚ)) := by rw [h]
    _ = _ := by ring

end HilbertBipartite
