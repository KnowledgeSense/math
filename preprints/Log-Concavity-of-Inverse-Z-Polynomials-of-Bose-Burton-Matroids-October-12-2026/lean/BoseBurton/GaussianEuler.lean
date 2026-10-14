import BoseBurton.KernelDuality
import BoseBurton.GaussianPartialAll

noncomputable section
namespace BoseBurton
open Finset

theorem gaussian_euler_term_dual (q : ℝ) (hq : 1<q) (n k : ℕ) (hk : k≤n) :
    (-1:ℝ)^k*q^(k.choose 2)*gaussian q n k=
      ((-1:ℝ)^n*q^(n.choose 2))*
        ((-1:ℝ)^(n-k)*(q⁻¹)^((n-k).choose 2)*gaussian q⁻¹ n (n-k)) := by
  have hq0 : q≠0 := by linarith
  rw [gaussian_dual q hq n k hk,gaussian_symm q⁻¹ n k hk]
  have he : k.choose 2+k*(n-k)+(n-k).choose 2=n.choose 2 := by
    have h := choose_two_add k (n-k)
    rw [Nat.add_sub_of_le hk] at h
    omega
  have hp : q^(k.choose 2)*q^(k*(n-k))=
      q^(n.choose 2)*(q⁻¹)^((n-k).choose 2) := by
    rw [← pow_add,← he,pow_add,inv_pow]
    field_simp
    simp only [pow_add]
  have hs : (-1:ℝ)^n*(-1)^(n-k)=(-1)^k := by
    rw [show n=k+(n-k) by omega,pow_add]
    rw [show k+(n-k)-k=n-k by omega,mul_assoc,← mul_pow]
    norm_num
  calc
    _ = (-1:ℝ)^k*(q^(k.choose 2)*q^(k*(n-k)))*gaussian q⁻¹ n k := by ring
    _ = _ := by rw [hp,← hs]; ring

theorem gaussian_euler_sum (q : ℝ) (hq : 1<q) (n : ℕ) (hn : 1≤n) :
    (∑ k∈range (n+1),(-1:ℝ)^k*q^(k.choose 2)*gaussian q n k)=0 := by
  have hq0 : 0<q := by linarith
  have he : (∑ k∈range (n+1),(-1:ℝ)^k*q^(k.choose 2)*gaussian q n k)=
      ((-1:ℝ)^n*q^(n.choose 2))*
      ∑ k∈range (n+1),(-1:ℝ)^(n-k)*(q⁻¹)^((n-k).choose 2)*gaussian q⁻¹ n (n-k) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    exact gaussian_euler_term_dual q hq n k (by simp only [mem_range] at hk; omega)
  rw [he]
  have href := sum_range_reflect
    (fun k=>(-1:ℝ)^k*(q⁻¹)^(k.choose 2)*gaussian q⁻¹ n k) (n+1)
  simp only [Nat.add_sub_cancel] at href
  rw [href,gaussian_partial_alternating_all q⁻¹ (inv_nonneg.mpr hq0.le)
    ((inv_lt_one₀ hq0).mpr hq) n n hn,ite_eq_right (by omega),mul_zero]

end BoseBurton
