import AperyMoments.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory
namespace AperyMoments

/-- Complete elliptic integral in the source's parameter convention. -/
def ellipticK (m : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))

theorem ellipticK_base_pos {m : ℝ} (hm : m < 1) (θ : ℝ) :
    0 < 1 - m * Real.sin θ ^ 2 := by
  have hs := Real.sin_sq_le_one θ
  have hs0 := sq_nonneg (Real.sin θ)
  by_cases hm0 : 0 ≤ m
  · nlinarith [mul_le_mul_of_nonneg_left hs hm0]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hm0) hs0
    linarith

theorem ellipticK_integrand_continuous {m : ℝ} (hm : m < 1) :
    Continuous (fun θ : ℝ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ))) := by
  apply Continuous.rpow_const (by fun_prop)
  intro θ
  exact Or.inl (ne_of_gt (ellipticK_base_pos hm θ))

theorem ellipticK_integrable {m : ℝ} (hm : m < 1) :
    IntervalIntegrable (fun θ : ℝ => (1 - m * Real.sin θ ^ 2) ^ (-(1 / 2 : ℝ)))
      volume 0 (Real.pi / 2) :=
  (ellipticK_integrand_continuous hm).intervalIntegrable _ _

theorem ellipticK_pos {m : ℝ} (hm : m < 1) : 0 < ellipticK m := by
  apply intervalIntegral.integral_pos (by positivity)
    (ellipticK_integrand_continuous hm).continuousOn
  · intro θ _
    exact (Real.rpow_pos_of_pos (ellipticK_base_pos hm θ) _).le
  · exact ⟨0, ⟨le_rfl, by positivity⟩,
      Real.rpow_pos_of_pos (ellipticK_base_pos hm 0) _⟩

theorem ellipticK_zero : ellipticK 0 = Real.pi / 2 := by
  simp [ellipticK]

theorem ellipticK_continuousOn : ContinuousOn ellipticK (Iio 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.rpow_const (by fun_prop)
  intro p
  exact Or.inl (ne_of_gt (ellipticK_base_pos p.1.property p.2))

end AperyMoments
