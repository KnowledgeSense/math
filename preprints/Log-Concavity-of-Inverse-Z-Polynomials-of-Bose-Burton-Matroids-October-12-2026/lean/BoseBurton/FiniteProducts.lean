import BoseBurton.ScalarDefinitions

noncomputable section
namespace BoseBurton
open Finset

@[simp] theorem qFactorial_zero (z : ℝ) : qFactorial z 0=1 := by simp [qFactorial]
@[simp] theorem qFactorial_succ (z : ℝ) (n : ℕ) :
    qFactorial z (n+1)=qFactorial z n*(1-z^(n+1)) := by simp [qFactorial,prod_range_succ]

theorem one_sub_pow_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (i : ℕ) (hi : 0< i) :
    0<1-z^i := sub_pos.mpr (pow_lt_one₀ hz0 hz1 (by omega))

theorem qFactorial_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) : 0<qFactorial z n := by
  apply prod_pos
  intro i _
  exact one_sub_pow_pos z hz0 hz1 (i+1) (by omega)

theorem gaussian_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) (hk : k≤n) :
    0<gaussian z n k := by
  rw [gaussian,ite_eq_left hk]
  exact div_pos (qFactorial_pos z hz0 hz1 n)
    (mul_pos (qFactorial_pos z hz0 hz1 k) (qFactorial_pos z hz0 hz1 (n-k)))

theorem gaussian_nonneg (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) :
    0≤gaussian z n k := by
  by_cases hk : k≤n
  · exact (gaussian_pos z hz0 hz1 n k hk).le
  · rw [gaussian,ite_eq_right hk]

theorem gaussian_zero_right (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) : gaussian z n 0=1 := by
  rw [gaussian,ite_eq_left (Nat.zero_le _),qFactorial_zero,Nat.sub_zero,one_mul]
  exact div_self (qFactorial_pos z hz0 hz1 n).ne'

theorem gaussian_self (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n : ℕ) : gaussian z n n=1 := by
  rw [gaussian,ite_eq_left le_rfl,Nat.sub_self,qFactorial_zero,mul_one]
  exact div_self (qFactorial_pos z hz0 hz1 n).ne'

theorem gaussian_symm (z : ℝ) (n k : ℕ) (hk : k≤n) : gaussian z n (n-k)=gaussian z n k := by
  rw [gaussian,ite_eq_left (Nat.sub_le _ _),gaussian,ite_eq_left hk,Nat.sub_sub_self hk,mul_comm]

@[simp] theorem fallingProduct_zero (z : ℝ) (k : ℕ) : fallingProduct z 0 k=1 := by simp [fallingProduct]
@[simp] theorem fallingProduct_succ (z : ℝ) (j k : ℕ) :
    fallingProduct z (j+1) k=fallingProduct z j k*(1-z^(k-(j+1))) := by
  simp [fallingProduct,prod_range_succ]

theorem fallingProduct_eq_zero (z : ℝ) (j k : ℕ) (hk : 1≤k) (hkj : k≤j) :
    fallingProduct z j k=0 := by
  apply prod_eq_zero (mem_range.mpr (show k-1<j by omega))
  rw [show k-(k-1+1)=0 by omega,pow_zero,sub_self]

theorem fallingProduct_pos (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (j k : ℕ) (hjk : j<k) :
    0<fallingProduct z j k := by
  apply prod_pos
  intro i hi
  exact one_sub_pow_pos z hz0 hz1 _ (by have := mem_range.mp hi; omega)

theorem fallingProduct_nonneg (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (j k : ℕ) :
    0≤fallingProduct z j k := by
  apply prod_nonneg
  intro i _
  exact sub_nonneg.mpr (pow_le_one₀ hz0 hz1.le)

@[simp] theorem pairedProduct_zero (z : ℝ) (r k : ℕ) : pairedProduct z r 0 k=1 := by simp [pairedProduct]

theorem pairedProduct_symm (z : ℝ) (r j k : ℕ) (hk : k≤r) :
    pairedProduct z r j (r-k)=pairedProduct z r j k := by
  rw [pairedProduct,pairedProduct,Nat.sub_sub_self hk,mul_comm]

theorem pairedProduct_nonneg (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (r j k : ℕ) :
    0≤pairedProduct z r j k :=
  mul_nonneg (fallingProduct_nonneg z hz0 hz1 j k) (fallingProduct_nonneg z hz0 hz1 j (r-k))

end BoseBurton
