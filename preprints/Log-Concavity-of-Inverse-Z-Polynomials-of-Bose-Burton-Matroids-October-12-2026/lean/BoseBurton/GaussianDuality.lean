import BoseBurton.GaussianFalling
import BoseBurton.KernelExponentAlgebra

noncomputable section
namespace BoseBurton
open Finset

theorem triangle_add (a b : ℕ) : (a+b+1).choose 2=(a+1).choose 2+(b+1).choose 2+a*b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : (a+(b+1)+1).choose 2=(a+b+1)+(a+b+1).choose 2 := by
      rw [show a+(b+1)+1=(a+b+1)+1 by omega,Nat.choose_succ_succ]; simp
    have h2 : (b+1+1).choose 2=(b+1)+(b+1).choose 2 := by rw [Nat.choose_succ_succ]; simp
    rw [h1,h2,ih]
    ring

theorem qFactorial_dual (q : ℝ) (hq : q≠0) (n : ℕ) :
    qFactorial q n=(-1:ℝ)^n*q^((n+1).choose 2)*qFactorial q⁻¹ n := by
  induction n with
  | zero => simp [qFactorial_zero]
  | succ n ih =>
    rw [qFactorial_succ,qFactorial_succ,ih]
    have htri : (n+1+1).choose 2=(n+1).choose 2+(n+1) := by
      rw [Nat.choose_succ_succ]; simp; omega
    rw [htri,pow_add,pow_succ (-1:ℝ) n]
    have hp : q^(n+1)*(q⁻¹)^(n+1)=1 := by rw [← mul_pow,mul_inv_cancel₀ hq,one_pow]
    linear_combination -(-1:ℝ)^n*q^((n+1).choose 2)*qFactorial q⁻¹ n*hp

theorem gaussian_dual (q : ℝ) (hq : 1<q) (n k : ℕ) (hk : k≤n) :
    gaussian q n k=q^(k*(n-k))*gaussian q⁻¹ n k := by
  have hq0 : 0<q := by linarith
  have hz0 : 0≤q⁻¹ := inv_nonneg.mpr hq0.le
  have hz1 : q⁻¹<1 := (inv_lt_one₀ hq0).mpr hq
  have hp (i : ℕ) := (qFactorial_pos q⁻¹ hz0 hz1 i).ne'
  have hqn := hq0.ne'
  have ht : (n+1).choose 2=(k+1).choose 2+(n-k+1).choose 2+k*(n-k) := by
    simpa only [Nat.add_sub_of_le hk] using triangle_add k (n-k)
  have hs : (-1:ℝ)^n=(-1)^k*(-1)^(n-k) := by rw [← pow_add,Nat.add_sub_of_le hk]
  simp only [gaussian,hk,ite_true]
  rw [qFactorial_dual q hqn n,qFactorial_dual q hqn k,qFactorial_dual q hqn (n-k),ht,hs]
  simp only [pow_add]
  field_simp [hp]

end BoseBurton
