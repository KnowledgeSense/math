import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

def eigenvaluePowerGap (q s d : ℝ) : ℝ :=
  ((s + d) / 2) ^ q + ((s - d) / 2) ^ q

theorem eigenvaluePowerGap_hasDerivAt (q s : ℝ) {d : ℝ} (hd : 0 < d) (hds : d < s) :
    HasDerivAt (eigenvaluePowerGap q s)
      (q / 2 * (((s + d) / 2) ^ (q - 1) - ((s - d) / 2) ^ (q - 1))) d := by
  have hu : 0 < (s + d) / 2 := by linarith
  have hv : 0 < (s - d) / 2 := by linarith
  have h1 := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hu.ne')).comp d
    (((hasDerivAt_const d s).add (hasDerivAt_id d)).div_const 2)
  have h2 := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hv.ne')).comp d
    (((hasDerivAt_const d s).sub (hasDerivAt_id d)).div_const 2)
  convert h1.add h2 using 1
  · rfl
  · ring

theorem eigenvaluePowerGap_monotone {q s : ℝ} (hq : 1 ≤ q) :
    MonotoneOn (eigenvaluePowerGap q s) (Set.Icc 0 s) := by
  have hcont : Continuous (eigenvaluePowerGap q s) := by
    unfold eigenvaluePowerGap
    have hp : Continuous (fun x : ℝ => x ^ q) := Real.continuous_rpow_const (by linarith)
    exact (hp.comp ((continuous_const.add continuous_id).div_const 2)).add
      (hp.comp ((continuous_const.sub continuous_id).div_const 2))
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont.continuousOn
  · intro d hd
    rw [interior_Icc] at hd
    exact (eigenvaluePowerGap_hasDerivAt q s hd.1 hd.2).differentiableAt.differentiableWithinAt
  · intro d hd
    rw [interior_Icc] at hd
    rw [(eigenvaluePowerGap_hasDerivAt q s hd.1 hd.2).deriv]
    obtain ⟨hd0, hds⟩ := hd
    have hv : 0 ≤ (s - d) / 2 := by linarith
    have hvu : (s - d) / 2 ≤ (s + d) / 2 := by linarith
    have hpower := Real.rpow_le_rpow hv hvu (sub_nonneg.mpr hq)
    exact mul_nonneg (by linarith) (sub_nonneg.mpr hpower)

theorem eigenvaluePowerGap_antitone {q s : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    AntitoneOn (eigenvaluePowerGap q s) (Set.Icc 0 s) := by
  have hcont : Continuous (eigenvaluePowerGap q s) := by
    unfold eigenvaluePowerGap
    have hp : Continuous (fun x : ℝ => x ^ q) := Real.continuous_rpow_const hq.le
    exact (hp.comp ((continuous_const.add continuous_id).div_const 2)).add
      (hp.comp ((continuous_const.sub continuous_id).div_const 2))
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) hcont.continuousOn
  · intro d hd
    rw [interior_Icc] at hd
    exact (eigenvaluePowerGap_hasDerivAt q s hd.1 hd.2).differentiableAt.differentiableWithinAt
  · intro d hd
    rw [interior_Icc] at hd
    rw [(eigenvaluePowerGap_hasDerivAt q s hd.1 hd.2).deriv]
    obtain ⟨hd0, hds⟩ := hd
    have hv : 0 < (s - d) / 2 := by linarith
    have hvu : (s - d) / 2 ≤ (s + d) / 2 := by linarith
    have hpower := Real.rpow_le_rpow_of_nonpos hv hvu (by linarith : q - 1 ≤ 0)
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hpower)

end

end ResearchMain.DiagonalSchatten
