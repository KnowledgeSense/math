import AperyMoments.LowerEllipticRight
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory
namespace AperyMoments

theorem ellipticK_mono {m n : ℝ} (hmn : m ≤ n) (hn : n < 1) : ellipticK m ≤ ellipticK n := by
  apply intervalIntegral.integral_mono (by positivity)
    (ellipticK_integrable (hmn.trans_lt hn)) (ellipticK_integrable hn)
  intro θ
  apply Real.rpow_le_rpow_of_nonpos (ellipticK_base_pos hn θ) _ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hmn (sq_nonneg (Real.sin θ))]

theorem lowerEllipticRealKernel_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (lowerEllipticRealKernel x) := by
  unfold lowerEllipticRealKernel
  apply Continuous.mul
  · exact Continuous.rpow_const (by fun_prop) (fun t => Or.inl (by positivity))
  · exact Continuous.rpow_const (by fun_prop) (fun t => Or.inl (by positivity))

theorem ellipticK_positive_half_integral {x : ℝ} (hx : 0 < x) :
    ellipticK (1 - x ^ 2) = 2 * ∫ t in (0 : ℝ)..1, lowerEllipticRealKernel x t := by
  have h := lowerEllipticIntegral_eq_half_right (z := (x : ℂ)) hx
  rw [lowerEllipticIntegral_ofReal hx, halfEllipticIntegral] at h
  simp_rw [lowerEllipticKernel_ofReal hx] at h
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- A simple integrable power bound suffices near the logarithmic singularity. -/
theorem ellipticK_complement_bound {x : ℝ} (hx : 0 < x) :
    ellipticK (1 - x ^ 2) ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
  rw [ellipticK_positive_half_integral hx]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hbound (t : ℝ) : lowerEllipticRealKernel x t ≤ x ^ (-(1 / 2 : ℝ)) := by
    have ha := Real.rpow_le_rpow_of_nonpos hx (show x ≤ t ^ 2 + x by nlinarith) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have hb := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
      (show 1 ≤ 1 + x * t ^ 2 by nlinarith [mul_nonneg hx.le (sq_nonneg t)]) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    rw [Real.one_rpow] at hb
    exact (mul_le_mul ha hb (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hx.le _)).trans_eq (mul_one _)
  have hi := intervalIntegral.integral_mono (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((lowerEllipticRealKernel_continuous hx).intervalIntegrable _ _) intervalIntegrable_const hbound
  simpa using hi

theorem quadratic_inverse_sqrt_eighth_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    (t ^ 2 + x) ^ (-(1 / 2 : ℝ)) ≤
      t ^ (-(3 / 4 : ℝ)) * x ^ (-(1 / 8 : ℝ)) := by
  have hA : 0 < t ^ 2 + x := by positivity
  have hpow : t ^ 6 * x ≤ (t ^ 2 + x) ^ 4 := by
    have h3 := pow_le_pow_left₀ (sq_nonneg t) (show t ^ 2 ≤ t ^ 2 + x by linarith) 3
    have hh := mul_le_mul h3 (show x ≤ t ^ 2 + x by nlinarith) hx.le (by positivity)
    convert hh using 1 <;> ring
  have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < t ^ 6 * x) hpow
    (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  rw [← Real.rpow_natCast_mul hA.le, Real.mul_rpow (by positivity) hx.le,
    ← Real.rpow_natCast_mul ht.le] at hr
  norm_num at hr
  exact hr

/-- An eighth-power bound gives finite fourth moments of the lattice-density singularity. -/
theorem ellipticK_complement_eighth_bound {x : ℝ} (hx : 0 < x) :
    ellipticK (1 - x ^ 2) ≤ 8 * x ^ (-(1 / 8 : ℝ)) := by
  rw [ellipticK_positive_half_integral hx]
  have hright : IntervalIntegrable (fun t : ℝ =>
      t ^ (-(3 / 4 : ℝ)) * x ^ (-(1 / 8 : ℝ))) volume 0 1 :=
    IntervalIntegrable.mul_const (intervalIntegral.intervalIntegrable_rpow' (by norm_num)) _
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) ((lowerEllipticRealKernel_continuous hx).intervalIntegrable _ _) hright
    (fun t ht => by
      have h1 := quadratic_inverse_sqrt_eighth_bound hx ht.1
      have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ 1 + x * t ^ 2 by nlinarith [mul_nonneg hx.le (sq_nonneg t)])
        (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      rw [Real.one_rpow] at h2
      exact (mul_le_mul h1 h2 (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg hx.le _))).trans_eq (mul_one _))
  rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ)))] at hbound
  norm_num at hbound
  nlinarith

end AperyMoments
