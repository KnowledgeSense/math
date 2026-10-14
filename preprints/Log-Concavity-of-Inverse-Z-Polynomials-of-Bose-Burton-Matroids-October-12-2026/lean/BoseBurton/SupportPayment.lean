import BoseBurton.SupportPaymentBounds

noncomputable section
namespace BoseBurton

theorem enteringWeightedProduct_ratio (z : ℝ) (hz0 : 0<z) (hz1 : z<1)
    (r s k : ℕ) (hsr : s<r) (hk : 1≤k) (hks : k≤s) (hr : 2*k+2≤r) :
    (positiveWeight z r s k*pairedProduct z r k (k+1))/
      (positiveWeight z r s (k-1)*pairedProduct z r (k-1) k)=
    z^(r-s+2*k)*(1-z^(s-k+1))*(1-z^(r-2*k-1))*(1-z^(r-2*k))/
      ((1-z^k)*(1-z^(r-k))*(1-z^(r-k-1))) := by
  rw [← div_mul_div_comm]
  have hw := positiveWeight_step_ratio z hz0 hz1 r s (k-1) hsr (by omega)
  rw [show k-1+1=k by omega,show r-s+2*(k-1)+2=r-s+2*k by omega,
    show s-(k-1)=s-k+1 by omega,show r-(k-1)-1=r-k by omega] at hw
  rw [hw,enteringProduct_ratio z hz0.le hz1 r k hk hr]
  have h := (one_sub_pow_pos z hz0.le hz1 k (by omega)).ne'
  field_simp

 theorem enteringWeightedProduct_bound (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hk : 2≤k) (hks : k≤s) (hr : 2*k+2≤r) :
    (positiveWeight z r s k*pairedProduct z r k (k+1))/
      (positiveWeight z r s (k-1)*pairedProduct z r (k-1) k)≤z^k/(1-z) := by
  have hz1 : z<1 := by linarith
  rw [enteringWeightedProduct_ratio z hz0 hz1 r s k hsr (by omega) hks hr]
  have hnon (i : ℕ) : 0≤1-z^i := by have := pow_le_one₀ hz0.le hz1.le (n:=i); linarith
  have hle (i : ℕ) : 1-z^i≤1 := by have := pow_nonneg hz0.le i; linarith
  have hb := three_factor_quotient_bound
    (1-z^(s-k+1)) (1-z^(r-2*k-1)) (1-z^(r-2*k))
    (1-z^k) (1-z^(r-k)) (1-z^(r-k-1)) (1-z)
    (hnon _) (hnon _) (hnon _) (hle _) (hle _) (hle _) (by linarith)
    (one_sub_pow_lower z hz0.le hz1.le k (by omega))
    (one_sub_pow_lower z hz0.le hz1.le (r-k) (by omega))
    (one_sub_pow_lower z hz0.le hz1.le (r-k-1) (by omega))
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hz0.le (r-s+2*k))
  have hp := payment_power_bound z hz0.le hzhalf (r-s) k (by omega) hk
  calc
    _ = z^(r-s+2*k)*((1-z^(s-k+1))*(1-z^(r-2*k-1))*(1-z^(r-2*k))/
      ((1-z^k)*(1-z^(r-k))*(1-z^(r-k-1)))) := by ring
    _ ≤ z^(r-s+2*k)*(1/(1-z)^3) := hm
    _ ≤ z^k/(1-z) := by simpa only [mul_one_div] using hp

theorem enteringWeightedProduct_payment (z : ℝ) (hz0 : 0<z) (hzhalf : z≤1/2)
    (r s k : ℕ) (hsr : s<r) (hk : 2≤k) (hks : k≤s) (hr : 2*k+2≤r) :
    positiveWeight z r s k*pairedProduct z r k (k+1)+
      positiveWeight z r s (k-1)*pairedProduct z r (k-1) (k+1)≤
      2*(positiveWeight z r s (k-1)*pairedProduct z r (k-1) k) := by
  have hz1 : z<1 := by linarith
  have hw := positiveWeight_pos z hz0 hz1 r s (k-1) hsr (by omega)
  have hQ := pairedProduct_pos z hz0.le hz1 r (k-1) k (by omega) (by omega)
  have hb := enteringWeightedProduct_bound z hz0 hzhalf r s k hsr hk hks hr
  have hp := precedingProduct_reserve z hz0.le hzhalf r k (by omega) hr
  have hh := le_trans hb hp
  have he : pairedProduct z r (k-1) (k+1)/pairedProduct z r (k-1) k=
      (positiveWeight z r s (k-1)*pairedProduct z r (k-1) (k+1))/
      (positiveWeight z r s (k-1)*pairedProduct z r (k-1) k) := by
    field_simp
  rw [he] at hh
  have h := (div_le_iff₀ (mul_pos hw hQ)).mp
    (show (positiveWeight z r s k*pairedProduct z r k (k+1)+
      positiveWeight z r s (k-1)*pairedProduct z r (k-1) (k+1))/
      (positiveWeight z r s (k-1)*pairedProduct z r (k-1) k)≤2 by
      rw [add_div]; linarith)
  exact h

end BoseBurton
