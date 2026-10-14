import BoseBurton.PairedRatios
import BoseBurton.WeightRatios

noncomputable section
namespace BoseBurton

theorem one_sub_pow_lower (z : ℝ) (hz0 : 0≤z) (hz1 : z≤1) (k : ℕ) (hk : 1≤k) :
    1-z≤1-z^k := by
  have h : z^k≤z := by simpa only [pow_one] using pow_le_pow_of_le_one hz0 hz1 hk
  linarith

theorem precedingProduct_reserve (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (r k : ℕ) (hk : 1≤k) (hr : 2*k+2≤r) :
    z^k/(1-z)≤2-pairedProduct z r (k-1) (k+1)/pairedProduct z r (k-1) k := by
  have hz1 : z<1 := by linarith
  have hd : 0<1-z := by linarith
  have hC := one_sub_pow_pos z hz0 hz1 (r-k-1) (by omega)
  have hpow : z^(r-k-1)≤z^(r-2*k) := pow_le_pow_of_le_one hz0 hz1.le (by omega)
  have hfrac : (1-z^(r-2*k))/(1-z^(r-k-1))≤1 := (div_le_one hC).mpr (by linarith)
  have hbase : 0≤(1-z^k)/(1-z) := div_nonneg (by have := pow_le_one₀ hz0 hz1.le (n:=k); linarith) hd.le
  have hb := mul_le_mul_of_nonneg_left hfrac hbase
  rw [mul_one,div_mul_div_comm,← precedingProduct_ratio z hz0 hz1 r k hk hr] at hb
  have hpay : z^k/(1-z)≤2-(1-z^k)/(1-z) := by
    apply (le_sub_iff_add_le).mpr
    rw [← add_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

theorem three_factor_quotient_bound (a b c A B C d : ℝ)
    ( _ha0 : 0≤a) (hb0 : 0≤b) (hc0 : 0≤c) (ha1 : a≤1) (hb1 : b≤1) (hc1 : c≤1)
    (hd : 0<d) (hA : d≤A) (hB : d≤B) (hC : d≤C) :
    a*b*c/(A*B*C)≤1/d^3 := by
  have hnum : a*b*c≤1 := by
    calc a*b*c ≤ 1*1*1 := mul_le_mul (mul_le_mul ha1 hb1 hb0 (by norm_num)) hc1 hc0 (by norm_num)
         _ = 1 := by ring
  have hden : d^3≤A*B*C := by
    have hA0 : 0≤A := le_trans hd.le hA
    have hB0 : 0≤B := le_trans hd.le hB
    have h := mul_le_mul (mul_le_mul hA hB hd.le hA0) hC hd.le (mul_nonneg hA0 hB0)
    nlinarith [h]
  exact div_le_div₀ (by norm_num) hnum (pow_pos hd 3) hden

theorem payment_power_bound (z : ℝ) (hz0 : 0≤z) (hzhalf : z≤1/2)
    (c k : ℕ) (hc : 1≤c) (hk : 2≤k) :
    z^(c+2*k)/(1-z)^3≤z^k/(1-z) := by
  have hz1 : z<1 := by linarith
  have hd : 0<1-z := by linarith
  have hp : z^(c+k)≤z^2 := pow_le_pow_of_le_one hz0 hz1.le (by omega)
  have hz : z^(c+k)≤(1-z)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (pow_nonneg hz0 k)) hd.le
  apply (div_le_div_iff₀ (pow_pos hd 3) hd).mpr
  have he : z^(c+2*k)=z^k*z^(c+k) := by rw [← pow_add]; congr 1; omega
  rw [he]
  nlinarith [hm]

end BoseBurton
