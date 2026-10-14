import ChowlaCosine.LocalForms
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ChowlaCosine

theorem error_margin :
    (5.27 : ℝ)*(0.99)^4 - 4.86*(1.01)^4 - 2*12.86*((1.01)^2/100)^2 =
      58226264657/25000000000000 := by norm_num

theorem error_margin_gt :
    (1/500 : ℝ) < (5.27 : ℝ)*(0.99)^4 - 4.86*(1.01)^4 - 2*12.86*((1.01)^2/100)^2 := by
  norm_num

theorem roth_coefficient : ((0.99 : ℝ)^2-1/3)/1.01 ≥ 1/2 := by norm_num

theorem selector_coefficient : (4 : ℝ)/0.99+8 ≤ 13 := by norm_num

theorem summed_error_absorption (B C n K : ℝ) (hB : 0 ≤ B) (hC : C ≤ 2*B)
    (h : (5.27*(0.99)^4-4.86*(1.01)^4)*B ≤
      12.86*((1.01)^2/100)^2*C + 5408*n*K^8) :
    B ≤ 2704000*n*K^8 := by
  norm_num at h
  nlinarith

theorem small_support_bound (n K : ℝ) (hK : 0.99 ≤ K) (hn : n < 3*K^2) :
    n ≤ 100000000*K^9 := by
  have hp : (0.99 : ℝ)^7 ≤ K^7 := pow_le_pow_left₀ (by norm_num) hK 7
  have hm : (3 : ℝ) ≤ 100000000*K^7 := by norm_num at hp; linarith
  calc
    n ≤ 3*K^2 := hn.le
    _ ≤ (100000000*K^7)*K^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg K)
    _ = _ := by ring

theorem large_support_bound (n K B : ℝ) (hn : 0 < n) (hK : 0 < K)
    (hlower : n^2/(6*K) ≤ B) (hupper : B ≤ 2704000*n*K^8) :
    n ≤ 100000000*K^9 := by
  have h1 : n^2 ≤ B*(6*K) := (div_le_iff₀ (by positivity)).mp hlower
  have h2 := mul_le_mul_of_nonneg_right hupper (by positivity : (0:ℝ) ≤ 6*K)
  have h3 : n*n ≤ n*(16224000*K^9) := by nlinarith [h1,h2]
  have h4 : n ≤ 16224000*K^9 := (mul_le_mul_iff_right₀ hn).mp h3
  calc
    n ≤ 16224000*K^9 := h4
    _ ≤ 100000000*K^9 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem cosine_power_bound (N K : ℝ) (hK : 0 ≤ K)
    (h : 2*N ≤ 100000000*(2*K)^9) : N ≤ 20^9*K^9 := by
  have hp : 0 ≤ K^9 := by positivity
  nlinarith

end ChowlaCosine
