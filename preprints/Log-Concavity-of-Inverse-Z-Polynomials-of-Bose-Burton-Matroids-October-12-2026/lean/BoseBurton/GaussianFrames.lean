import BoseBurton.GaussianDuality

noncomputable section
namespace BoseBurton
open Finset

def frameProduct (q : ℝ) (n k : ℕ) : ℝ := ∏ i∈range k,(q^n-q^i)

theorem frameProduct_falling (q : ℝ) (n k : ℕ) (hk : k≤n) :
    frameProduct q n k=(-1:ℝ)^k*q^(k.choose 2)*fallingProduct q k (n+1) := by
  induction k with
  | zero => simp [frameProduct,fallingProduct_zero]
  | succ k ih =>
    rw [frameProduct,prod_range_succ]
    change frameProduct q n k*(q^n-q^k)=_
    rw [ih (by omega),fallingProduct_succ]
    have he : (k+1).choose 2=k.choose 2+k := by rw [Nat.choose_succ_succ]; simp; omega
    simp only [he,pow_add,pow_one,show n+1-(k+1)=n-k by omega]
    have hp : q^k*q^(n-k)=q^n := by rw [← pow_add,Nat.add_sub_of_le (by omega)]
    linear_combination -(-1:ℝ)^k*q^(k.choose 2)*fallingProduct q k (n+1)*hp

theorem qFactorial_ne_zero_above_one (q : ℝ) (hq : 1<q) (n : ℕ) : qFactorial q n≠0 := by
  have hq0 : 0<q := by linarith
  rw [qFactorial_dual q hq0.ne' n]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq0.ne'))
    (qFactorial_pos q⁻¹ (inv_nonneg.mpr hq0.le) ((inv_lt_one₀ hq0).mpr hq) n).ne'

theorem frameProduct_quotient (q : ℝ) (hq : 1<q) (n k : ℕ) (hk : k≤n) :
    frameProduct q n k/frameProduct q k k=gaussian q n k := by
  have hp (i : ℕ) := qFactorial_ne_zero_above_one q hq i
  have hq0 : q≠0 := by linarith
  have hf (a b : ℕ) (hab : a≤b) : fallingProduct q a (b+1)=qFactorial q b/qFactorial q (b-a) := by
    apply (eq_div_iff (hp _)).mpr
    simpa only [Nat.add_sub_cancel] using fallingProduct_factorial_cleared q a (b+1) (by omega)
  rw [frameProduct_falling q n k hk,frameProduct_falling q k k le_rfl,hf k n hk,hf k k le_rfl]
  simp only [Nat.sub_self,qFactorial_zero,div_one,gaussian,hk,ite_true]
  field_simp [hp]

end BoseBurton
