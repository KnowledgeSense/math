import BoseBurton.GaussianIdentities

noncomputable section
namespace BoseBurton

theorem one_sub_pow_strict_step (z : ℝ) (hz0 : 0<z) (hz1 : z<1) (k : ℕ) :
    1-z^k<1-z^(k+1) := by
  have h := mul_lt_mul_of_pos_left hz1 (pow_pos hz0 k)
  rw [← pow_succ,mul_one] at h
  linarith

theorem gaussian_adjacent_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) (n k : ℕ) (hk : k<n) :
    gaussian z n (k+1)/gaussian z n k=(1-z^(n-k))/(1-z^(k+1)) := by
  apply (div_eq_div_iff (gaussian_pos z hz0 hz1 n k (by omega)).ne'
    (one_sub_pow_pos z hz0 hz1 (k+1) (by omega)).ne').mpr
  simpa only [mul_comm] using gaussian_adjacent z hz0 hz1 n k hk

theorem gaussian_strict_log_concave (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (n k : ℕ) (hk : 1≤k) (hkn : k<n) :
    gaussian z n (k-1)*gaussian z n (k+1)<(gaussian z n k)^2 := by
  have hkp := gaussian_pos z hz0.le hz1 n k (by omega)
  have hkm := gaussian_pos z hz0.le hz1 n (k-1) (by omega)
  have hA := one_sub_pow_pos z hz0.le hz1 k (by omega)
  have hA1 := one_sub_pow_pos z hz0.le hz1 (k+1) (by omega)
  have hB := one_sub_pow_pos z hz0.le hz1 (n-k) (by omega)
  have hB1 := one_sub_pow_pos z hz0.le hz1 (n-k+1) (by omega)
  have hAl := one_sub_pow_strict_step z hz0 hz1 k
  have hBl := one_sub_pow_strict_step z hz0 hz1 (n-k)
  have hrat : (1-z^(n-k))/(1-z^(k+1))<(1-z^(n-k+1))/(1-z^k) := by
    apply (div_lt_div_iff₀ hA1 hA).mpr
    exact mul_lt_mul hBl hAl.le hA hB1.le
  have hlow := gaussian_adjacent_ratio z hz0.le hz1 n (k-1) (by omega)
  rw [show k-1+1=k by omega,show n-(k-1)=n-k+1 by omega] at hlow
  rw [← gaussian_adjacent_ratio z hz0.le hz1 n k hkn,← hlow] at hrat
  have h := (div_lt_div_iff₀ hkp hkm).mp hrat
  simpa only [mul_comm,pow_two] using h

/-- A positive discretely concave factor preserves strict Gaussian log-concavity. -/
theorem gaussian_times_concave_strict (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (n k : ℕ) (hk : 1≤k) (hkn : k<n) (a b c : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hconc : a+c≤2*b) :
    (gaussian z n (k-1)*a)*(gaussian z n (k+1)*c)<(gaussian z n k*b)^2 := by
  have hlog : a*c≤b^2 := by nlinarith [sq_nonneg (a-c)]
  have hg := gaussian_strict_log_concave z hz0 hz1 n k hk hkn
  have hgp := mul_pos (gaussian_pos z hz0.le hz1 n (k-1) (by omega))
    (gaussian_pos z hz0.le hz1 n (k+1) (by omega))
  have h1 := mul_lt_mul_of_pos_right hg (mul_pos ha hc)
  have h2 := mul_le_mul_of_nonneg_left hlog (sq_nonneg (gaussian z n k))
  nlinarith

end BoseBurton
