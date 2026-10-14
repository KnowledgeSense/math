import BoseBurton.FiniteProducts

noncomputable section
namespace BoseBurton
open Finset

theorem gaussian_outside (z : ℝ) (n k : ℕ) (hk : n<k) : gaussian z n k=0 := by
  rw [gaussian,ite_eq_right (by omega)]

theorem gaussian_adjacent (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) (hk : k<n) :
    gaussian z n (k+1)*(1-z^(k+1))=gaussian z n k*(1-z^(n-k)) := by
  have hp := (qFactorial_pos z hz0 hz1 n).ne'
  have hkf := (qFactorial_pos z hz0 hz1 k).ne'
  have hnf := (qFactorial_pos z hz0 hz1 (n-(k+1))).ne'
  have hkz := (one_sub_pow_pos z hz0 hz1 (k+1) (by omega)).ne'
  have hnz := (one_sub_pow_pos z hz0 hz1 (n-k) (by omega)).ne'
  rw [gaussian,ite_eq_left (by omega),gaussian,ite_eq_left (by omega),qFactorial_succ]
  have hf : qFactorial z (n-k)=qFactorial z (n-(k+1))*(1-z^(n-k)) := by
    have he : n-k=(n-(k+1))+1 := by omega
    conv_lhs => rw [he,qFactorial_succ]
    rw [← he]
  rw [hf]
  field_simp

theorem gaussian_pascal_succ (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) :
    gaussian z (n+1) (k+1)=z^(k+1)*gaussian z n (k+1)+gaussian z n k := by
  by_cases hkn : k<n
  · have hkf := (qFactorial_pos z hz0 hz1 k).ne'
    have hnf := (qFactorial_pos z hz0 hz1 (n-k-1)).ne'
    have hkz := (one_sub_pow_pos z hz0 hz1 (k+1) (by omega)).ne'
    have hnz := (one_sub_pow_pos z hz0 hz1 (n-k) (by omega)).ne'
    have hp := (qFactorial_pos z hz0 hz1 n).ne'
    rw [gaussian,ite_eq_left (by omega),gaussian,ite_eq_left (by omega),gaussian,ite_eq_left (by omega)]
    rw [show n+1-(k+1)=n-k by omega,show n-(k+1)=n-k-1 by omega,qFactorial_succ z n,qFactorial_succ z k]
    have hf : qFactorial z (n-k)=qFactorial z (n-k-1)*(1-z^(n-k)) := by
      have he : n-k=(n-k-1)+1 := by omega
      conv_lhs => rw [he,qFactorial_succ]
      rw [← he]
    rw [hf]
    have hzpow : z^(k+1)*z^(n-k)=z^(n+1) := by rw [← pow_add]; congr 1; omega
    field_simp
    rw [← hzpow]
    ring
  · by_cases hke : k=n
    · subst k
      rw [gaussian_self z hz0 hz1,gaussian_outside z n (n+1) (by omega),
        gaussian_self z hz0 hz1,mul_zero,zero_add]
    · rw [gaussian_outside z (n+1) (k+1) (by omega),gaussian_outside z n (k+1) (by omega),
        gaussian_outside z n k (by omega),mul_zero,add_zero]

end BoseBurton
