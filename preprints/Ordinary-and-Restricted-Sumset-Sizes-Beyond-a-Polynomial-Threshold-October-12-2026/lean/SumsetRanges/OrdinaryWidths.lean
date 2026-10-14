import SumsetRanges.LargeParameters

namespace SumsetRanges

theorem ordinary_shared_width {h k c : ℕ} (hh : 3≤h) (hc : (32*h^3)^10≤c)
    (hkc : sparseThreshold k≤c) : 16*h*k≤sharedCap c*(sharedCap c-1) := by
  have hc32 := (large_c_elementary (by omega : 1≤h) hc).1
  have cp : 0<c := by omega
  have hk := k_le_four_c_rpow (by omega : 1≤c) hkc
  have hp := shared_product_lower (by omega : 1≤h) hc
  have hr : (256 : ℝ)*h≤(c : ℝ)^((6 : ℝ)/35) := by
    have hb : (((32*h^3:ℕ)^10:ℕ):ℝ)^((6:ℝ)/35)≤(c:ℝ)^((6:ℝ)/35) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hc) (by norm_num)
    have he : (((32*h^3:ℕ)^10:ℕ):ℝ)^((6:ℝ)/35)=
        (32*(h:ℝ)^3)^((12:ℝ)/7) := by
      push_cast
      rw [←Real.rpow_natCast_mul (by positivity)]
      norm_num
    rw [he] at hb
    have hs : (32*(h:ℝ)^3)≤(32*(h:ℝ)^3)^((12:ℝ)/7) := by
      have hbase : (1:ℝ)≤32*(h:ℝ)^3 := by
        have hh' : (3:ℝ)≤h := by exact_mod_cast hh
        have hp : (1:ℝ)≤(h:ℝ)^3 := by exact_mod_cast Nat.one_le_pow 3 h (by omega : 1≤h)
        nlinarith
      simpa using Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1:ℝ)≤12/7)
    have hh' : (3:ℝ)≤h := by exact_mod_cast hh
    have hpoly : (256:ℝ)*h≤32*(h:ℝ)^3 := by
      have hh2 : (9:ℝ)≤(h:ℝ)^2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hh2 (Nat.cast_nonneg h)
      nlinarith
    exact hpoly.trans (hs.trans hb)
  have hm := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg (Nat.cast_nonneg c) ((10:ℝ)/7))
  have he : (c:ℝ)^((6:ℝ)/35)*(c:ℝ)^((10:ℝ)/7)=(c:ℝ)^((8:ℝ)/5) := by
    rw [←Real.rpow_add (by exact_mod_cast cp)]
    norm_num
  rw [he] at hm
  have hmul := mul_le_mul_of_nonneg_left hk (by positivity : (0:ℝ)≤16*h)
  have hresult : (16:ℝ)*h*k≤(sharedCap c:ℝ)*(sharedCap c-1:ℕ) := by nlinarith
  exact_mod_cast hresult

end SumsetRanges
