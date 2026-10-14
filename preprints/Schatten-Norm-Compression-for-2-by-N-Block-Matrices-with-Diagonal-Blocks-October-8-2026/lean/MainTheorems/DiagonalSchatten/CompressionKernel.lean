import MainTheorems.DiagonalSchatten.GramBoundary
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ResearchMain.DiagonalSchatten

noncomputable section

def kernelFirst (k a c u v : ℝ) : ℝ := k * a + (k + 1) * c * v / u
def kernelSecond (k b c u v : ℝ) : ℝ := k * b + (k + 1) * c * u / v

theorem compressionKernel_determinant (k a b c u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    kernelFirst k a c u v * kernelSecond k b c u v - c ^ 2 =
      k * (k * a * b + (k + 2) * c ^ 2 + (k + 1) * c * (a * u / v + b * v / u)) := by
  unfold kernelFirst kernelSecond
  field_simp [hu, hv]
  ring

theorem weighted_ratio_ge {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) :
    2 * Real.sqrt (a * b) ≤ a * u / v + b * v / u := by
  have hra := Real.sq_sqrt ha.le
  have hrb := Real.sq_sqrt hb.le
  have hroot : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha.le b
  have hs := sq_nonneg (Real.sqrt a * u - Real.sqrt b * v)
  have hidSq : (Real.sqrt a * u - Real.sqrt b * v) ^ 2 =
      a * u ^ 2 + b * v ^ 2 - 2 * Real.sqrt a * Real.sqrt b * u * v := by
    rw [sub_sq, mul_pow, mul_pow, hra, hrb]
    ring
  rw [hidSq] at hs
  have hsq : 2 * Real.sqrt (a * b) * u * v ≤ a * u ^ 2 + b * v ^ 2 := by
    rw [hroot]
    nlinarith
  have hid : (a * u / v + b * v / u) * (u * v) = a * u ^ 2 + b * v ^ 2 := by
    field_simp [hu.ne', hv.ne']
  apply (le_of_mul_le_mul_right ?_ (mul_pos hu hv))
  rw [hid]
  nlinarith

theorem compressionKernel_upper {k a b c u v : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) :
    0 < kernelFirst k a c u v ∧
      0 < kernelFirst k a c u v * kernelSecond k b c u v - c ^ 2 := by
  constructor
  · unfold kernelFirst
    positivity
  · rw [compressionKernel_determinant _ _ _ _ _ _ hu.ne' hv.ne']
    positivity

theorem compressionKernel_lower {k a b c u v : ℝ}
    (hk1 : -1 < k) (hk : k < 0) (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hdet : c ^ 2 < a * b) (hu : 0 < u) (hv : 0 < v) :
    kernelFirst k a c u v < 0 ∧
      0 < kernelFirst k a c u v * kernelSecond k b c u v - c ^ 2 := by
  have hbeta : 0 < k + 1 := by linarith
  have hk2 : 0 < k + 2 := by linarith
  have hfirst : kernelFirst k a c u v < 0 := by
    unfold kernelFirst
    exact add_neg (mul_neg_of_neg_of_pos hk ha)
      (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hbeta hc) hv) hu)
  refine ⟨hfirst, ?_⟩
  let rho := Real.sqrt (a * b)
  let d := -c
  have hrho : 0 < rho := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hd : 0 < d := neg_pos.mpr hc
  have hrhosq : rho ^ 2 = a * b := Real.sq_sqrt (mul_pos ha hb).le
  have hrd : d < rho := by dsimp [d]; nlinarith
  have hratio := weighted_ratio_ge ha hb hu hv
  change 2 * rho ≤ a * u / v + b * v / u at hratio
  have hco : 0 < (k + 1) * d := mul_pos hbeta hd
  have hbound : k * a * b + (k + 2) * d ^ 2 -
      (k + 1) * d * (a * u / v + b * v / u) ≤
        k * a * b + (k + 2) * d ^ 2 - 2 * (k + 1) * d * rho := by
    have hmul := mul_le_mul_of_nonneg_left hratio hco.le
    linarith
  have hid : k * a * b + (k + 2) * d ^ 2 - 2 * (k + 1) * d * rho =
      (rho - d) * (k * rho - (k + 2) * d) := by
    calc
      _ = k * rho ^ 2 + (k + 2) * d ^ 2 - 2 * (k + 1) * d * rho := by
        rw [hrhosq]
        ring
      _ = _ := by ring
  have hneg : k * a * b + (k + 2) * d ^ 2 - 2 * (k + 1) * d * rho < 0 := by
    rw [hid]
    have hkr := mul_neg_of_neg_of_pos hk hrho
    have hkd := mul_pos hk2 hd
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hrd) (by linarith)
  have hbr : k * a * b + (k + 2) * c ^ 2 +
      (k + 1) * c * (a * u / v + b * v / u) < 0 := by
    dsimp [d] at hbound hneg
    nlinarith
  rw [compressionKernel_determinant _ _ _ _ _ _ hu.ne' hv.ne']
  exact mul_pos_of_neg_of_neg hk hbr

theorem compressionKernel_quadratic_upper {k a b c u v : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (s t : ℝ) :
    0 ≤ kernelFirst k a c u v * s ^ 2 - 2 * c * s * t + kernelSecond k b c u v * t ^ 2 := by
  obtain ⟨hfirst, hdet⟩ := compressionKernel_upper hk ha hb hc hu hv
  have h := symmetric2_nonnegative (kernelFirst k a c u v) (kernelSecond k b c u v)
    (-c) s t hfirst (by nlinarith)
  convert h using 1; ring

theorem compressionKernel_quadratic_lower {k a b c u v : ℝ}
    (hk1 : -1 < k) (hk : k < 0) (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (hdet : c ^ 2 < a * b) (hu : 0 < u) (hv : 0 < v) (s t : ℝ) :
    kernelFirst k a c u v * s ^ 2 - 2 * c * s * t + kernelSecond k b c u v * t ^ 2 ≤ 0 := by
  obtain ⟨hfirst, hdetK⟩ := compressionKernel_lower hk1 hk ha hb hc hdet hu hv
  have h := symmetric2_nonnegative (-kernelFirst k a c u v) (-kernelSecond k b c u v)
    c s t (neg_pos.mpr hfirst) (by nlinarith)
  linarith

end

end ResearchMain.DiagonalSchatten
