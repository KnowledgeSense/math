import BoseBurton.PairedConcavity

noncomputable section
namespace BoseBurton

theorem fallingProduct_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (j k : ℕ) (hjk : j<k) :
    fallingProduct z j (k+1)/fallingProduct z j k=(1-z^k)/(1-z^(k-j)) := by
  apply (div_eq_div_iff (fallingProduct_pos z hz0 hz1 j k hjk).ne'
    (one_sub_pow_pos z hz0 hz1 (k-j) (by omega)).ne').mpr
  simpa only [mul_comm] using fallingProduct_ratio_cleared z j k

theorem fallingProduct_reverse_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (j k : ℕ) (hjk : j<k) :
    fallingProduct z j k/fallingProduct z j (k+1)=(1-z^(k-j))/(1-z^k) := by
  apply (div_eq_div_iff (fallingProduct_pos z hz0 hz1 j (k+1) (by omega)).ne'
    (one_sub_pow_pos z hz0 hz1 k (by omega)).ne').mpr
  simpa only [mul_comm] using (fallingProduct_ratio_cleared z j k).symm

theorem pairedProduct_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r j k : ℕ) (hleft : j<k) (hright : j+1<r-k) :
    pairedProduct z r j (k+1)/pairedProduct z r j k=
      (1-z^k)*(1-z^(r-k-j-1))/((1-z^(k-j))*(1-z^(r-k-1))) := by
  unfold pairedProduct
  rw [show r-(k+1)=r-k-1 by omega]
  have he : r-k=(r-k-1)+1 := by omega
  have h := fallingProduct_reverse_ratio z hz0 hz1 j (r-k-1) (by omega)
  rw [← he,show r-k-1-j=r-k-j-1 by omega] at h
  rw [← div_mul_div_comm,fallingProduct_ratio z hz0 hz1 j k hleft,h,div_mul_div_comm]

theorem precedingProduct_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r k : ℕ) (hk : 1≤k) (hr : 2*k+2≤r) :
    pairedProduct z r (k-1) (k+1)/pairedProduct z r (k-1) k=
      (1-z^k)*(1-z^(r-2*k))/((1-z)*(1-z^(r-k-1))) := by
  rw [pairedProduct_ratio z hz0 hz1 r (k-1) k (by omega) (by omega),
    show k-(k-1)=1 by omega,show r-k-(k-1)-1=r-2*k by omega,pow_one]

theorem enteringProduct_ratio (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r k : ℕ) (hk : 1≤k) (hr : 2*k+2≤r) :
    pairedProduct z r k (k+1)/pairedProduct z r (k-1) k=
      (1-z^k)*(1-z^(r-2*k-1))*(1-z^(r-2*k))/(1-z^(r-k-1)) := by
  unfold pairedProduct
  have he : k=(k-1)+1 := by omega
  conv_lhs => lhs; lhs; rw [he,fallingProduct_shift]
  conv_lhs => lhs; rhs; rw [he,fallingProduct_succ,← he]
  rw [show r-(k+1)=r-k-1 by omega,show r-k-1-k=r-2*k-1 by omega]
  have hF := (fallingProduct_pos z hz0 hz1 (k-1) k (by omega)).ne'
  have hG := (fallingProduct_pos z hz0 hz1 (k-1) (r-k) (by omega)).ne'
  have hz := (one_sub_pow_pos z hz0 hz1 (r-k-1) (by omega)).ne'
  have hh := fallingProduct_reverse_ratio z hz0 hz1 (k-1) (r-k-1) (by omega)
  rw [show r-k-1+1=r-k by omega,show r-k-1-(k-1)=r-2*k by omega] at hh
  have hc := (div_eq_div_iff hG hz).mp hh
  rw [← he]
  field_simp
  linear_combination (1-z^k)*(1-z^(r-2*k-1))*hc

end BoseBurton
