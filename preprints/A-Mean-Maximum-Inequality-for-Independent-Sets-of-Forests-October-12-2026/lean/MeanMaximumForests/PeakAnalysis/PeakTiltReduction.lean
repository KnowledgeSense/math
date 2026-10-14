import MeanMaximumForests.PeakAnalysis.TiltMeanBounds
import MeanMaximumForests.PeakAnalysis.TiltCoefficient

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Set

/-- Local adjacent-mass estimates at tilted means suffice for the weak-peak lower bound.
This is an auxiliary reduction; its explicit local-mass hypothesis is not asserted here. -/
theorem weakLocalPeak_gap_of_tilted_mass_bound : ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.IsAcyclic →
      5 ≤ Fintype.card V → ∀ k : ℕ, WeakLocalPeak G k → ∀ η : ℝ, 0 < η →
      (∀ t ∈ Icc (Real.log (1 / 4)) 0, graphTiltMean G t = k →
        Real.exp (-η) * graphTiltSizeMass G t k < graphTiltSizeMass G t (k + 1)) →
      graphMean G - k < C * Fintype.card V * η := by
  obtain ⟨C, hC, hgap⟩ := forest_tilt_mean_gap
  refine ⟨C, hC, ?_⟩
  intro V _ _ G hG hn k hk η hη hmass
  have hn0 : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hCn : 0 < C * Fintype.card V := mul_pos hC hn0
  by_cases hkm : (k : ℝ) ≤ graphMean G
  · obtain ⟨t, ht, hmean⟩ := weakLocalPeak_tilt_mean G hG hn hk hkm
    have hstep := (hmass t ht hmean).trans_le (weakLocalPeak_tilt_mass_step G t hk)
    have hp := graphTiltSizeMass_pos G t hk.1
    have hexp : Real.exp (-η) < Real.exp t :=
      (mul_lt_mul_iff_left₀ hp).mp hstep
    have htη : -η < t := Real.exp_lt_exp.mp hexp
    have hg := hgap G hG t ht.2
    rw [hmean] at hg
    exact hg.trans_lt (mul_lt_mul_of_pos_left (by linarith : -t < η) hCn)
  · have hle : graphMean G - (k : ℝ) ≤ 0 := by linarith
    exact hle.trans_lt (mul_pos hCn hη)

end MeanMaximumForests.PeakAnalysis
