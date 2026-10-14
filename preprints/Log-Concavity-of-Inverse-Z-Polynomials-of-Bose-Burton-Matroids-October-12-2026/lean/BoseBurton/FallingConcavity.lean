import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton
open Finset

theorem fallingProduct_shift (z : ℝ) (j k : ℕ) :
    fallingProduct z (j+1) (k+1)=(1-z^k)*fallingProduct z j k := by
  rw [fallingProduct,prod_range_succ']
  simp only [Nat.add_sub_cancel_right]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 2
  omega

def fallingIncrement (z : ℝ) (j k : ℕ) : ℝ := fallingProduct z j (k+1)-fallingProduct z j k

theorem fallingIncrement_formula (z : ℝ) (j k : ℕ) (hj : 1≤j) (hjk : j≤k) :
    fallingIncrement z j k=z^(k-j)*(1-z^j)*fallingProduct z (j-1) k := by
  have he : j=(j-1)+1 := by omega
  unfold fallingIncrement
  conv_lhs => lhs; rw [he,fallingProduct_shift]
  conv_lhs => rhs; rw [he,fallingProduct_succ,← he]
  have hp : z^k=z^(k-j)*z^j := by rw [← pow_add,Nat.sub_add_cancel hjk]
  rw [hp]
  ring

theorem fallingIncrement_nonneg (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (j k : ℕ) :
    0≤fallingIncrement z j k := by
  by_cases hj : j=0
  · subst j
    simp [fallingIncrement]
  · by_cases hjk : j≤k
    · rw [fallingIncrement_formula z j k (by omega) hjk]
      exact mul_nonneg (mul_nonneg (pow_nonneg hz0 _) (sub_nonneg.mpr (pow_le_one₀ hz0 hz1.le)))
        (fallingProduct_nonneg z hz0 hz1 _ _)
    · by_cases hk : k=0
      · subst k
        have hzero : fallingProduct z j 0=0 := by
          rw [show j=(j-1)+1 by omega,fallingProduct_succ]
          simp
        rw [fallingIncrement,hzero,sub_zero]
        exact fallingProduct_nonneg z hz0 hz1 _ _
      · rw [fallingIncrement,fallingProduct_eq_zero z j k (by omega) (by omega),sub_zero]
        exact fallingProduct_nonneg z hz0 hz1 _ _

theorem fallingProduct_mono (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (j : ℕ) :
    Monotone (fallingProduct z j) := by
  apply monotone_nat_of_le_succ
  intro k
  exact sub_nonneg.mp (fallingIncrement_nonneg z hz0 hz1 j k)

theorem fallingProduct_ratio_cleared (z : ℝ) (j k : ℕ) :
    fallingProduct z j (k+1)*(1-z^(k-j))=fallingProduct z j k*(1-z^k) := by
  cases j with
  | zero => simp
  | succ j =>
    rw [fallingProduct_shift,fallingProduct_succ]
    ring

theorem fallingIncrement_ratio_cleared (z : ℝ) (j k : ℕ) (hj : 1≤j) (hjk : j≤k) :
    fallingIncrement z j (k+1)*(1-z^(k-j+1))=
      z*(1-z^k)*fallingIncrement z j k := by
  rw [fallingIncrement_formula z j (k+1) hj (by omega),fallingIncrement_formula z j k hj hjk,
    show k+1-j=(k-j)+1 by omega,pow_succ]
  have h := fallingProduct_ratio_cleared z (j-1) k
  rw [show k-(j-1)=k-j+1 by omega] at h
  calc
    _ = (z^(k-j)*z*(1-z^j))*(fallingProduct z (j-1) (k+1)*(1-z^(k-j+1))) := by ring
    _ = _ := by rw [h]; ring

theorem fallingIncrement_decreasing (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (j k : ℕ) (hj : 1≤j) (hjk : j≤k) : fallingIncrement z j (k+1)≤fallingIncrement z j k := by
  have hz1 : z<1 := by linarith
  have hden := one_sub_pow_pos z hz0 hz1 (k-j+1) (by omega)
  have hp : z^(k-j+1)≤z := by
    simpa only [pow_one] using pow_le_pow_of_le_one hz0 hz1.le (show 1≤k-j+1 by omega)
  have hn : 0≤z^k := pow_nonneg hz0 k
  have hb : z*(1-z^k)≤1-z^(k-j+1) := by nlinarith
  have hD := fallingIncrement_nonneg z hz0 hz1 j k
  have he := fallingIncrement_ratio_cleared z j k hj hjk
  have hm := mul_le_mul_of_nonneg_right hb hD
  nlinarith

theorem fallingProduct_concave (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (j k : ℕ) (hjk : j+1≤k) :
    fallingProduct z j (k-1)+fallingProduct z j (k+1)≤2*fallingProduct z j k := by
  by_cases hj : j=0
  · subst j; norm_num
  · have h := fallingIncrement_decreasing z hz0 hzhalf j (k-1) (by omega) (by omega)
    rw [show k-1+1=k by omega] at h
    unfold fallingIncrement at h
    rw [show k-1+1=k by omega] at h
    linarith

end BoseBurton
