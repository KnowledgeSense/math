import MainTheorems.DiagonalSchatten.SymmetricPowerPositivity

namespace ResearchMain.DiagonalSchatten

noncomputable section

theorem continuous_symmetricGap : Continuous symmetricGap := by
  unfold symmetricGap
  fun_prop

theorem continuous_symmetricPlus : Continuous symmetricPlus := by
  unfold symmetricPlus
  exact (((continuous_apply 0).add (continuous_apply 1)).add continuous_symmetricGap).div_const 2

theorem continuous_symmetricMinus : Continuous symmetricMinus := by
  unfold symmetricMinus
  exact (((continuous_apply 0).add (continuous_apply 1)).sub continuous_symmetricGap).div_const 2

theorem continuousAt_symmetricPowerVariation (r : ℝ) (m Z : Fin 3 → ℝ)
    (hc : m 2 ≠ 0) (hp : symmetricPlus m ≠ 0) (hm : symmetricMinus m ≠ 0) :
    ContinuousAt (fun n => symmetricPowerVariation r n Z) m := by
  have hg := continuous_symmetricGap.continuousAt (x := m)
  have hplus := continuous_symmetricPlus.continuousAt (x := m)
  have hminus := continuous_symmetricMinus.continuousAt (x := m)
  have hg0 := (symmetricGap_positive m hc).ne'
  have hplusPower := hplus.rpow_const (p := r) (Or.inl hp)
  have hminusPower := hminus.rpow_const (p := r) (Or.inl hm)
  have hplusDerivative := hplus.rpow_const (p := r - 1) (Or.inl hp)
  have hminusDerivative := hminus.rpow_const (p := r - 1) (Or.inl hm)
  have hd : ContinuousAt (symmetricDividedPower r) m := (hplusPower.sub hminusPower).div hg hg0
  have hgv : ContinuousAt (fun n => symmetricGapVariation n Z) m := by
    unfold symmetricGapVariation
    exact (show ContinuousAt (fun n : Fin 3 → ℝ =>
      (n 0 - n 1) * (Z 0 - Z 1) + 4 * n 2 * Z 2) m by fun_prop).div hg hg0
  have hpv : ContinuousAt (fun n => symmetricPlusVariation n Z) m := by
    unfold symmetricPlusVariation
    exact (continuousAt_const.add hgv).div_const 2
  have hmv : ContinuousAt (fun n => symmetricMinusVariation n Z) m := by
    unfold symmetricMinusVariation
    exact (continuousAt_const.sub hgv).div_const 2
  have hdv : ContinuousAt (fun n => symmetricDividedPowerVariation r n Z) m := by
    unfold symmetricDividedPowerVariation
    exact ((((hplusDerivative.const_mul r).mul hpv).sub
      ((hminusDerivative.const_mul r).mul hmv)).sub (hd.mul hgv)).div hg hg0
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact (((hminusDerivative.const_mul r).mul hmv).add
      (hdv.mul ((continuous_apply 0).continuousAt.sub hminus))).add
      (hd.mul (continuousAt_const.sub hmv))
  · exact (((hminusDerivative.const_mul r).mul hmv).add
      (hdv.mul ((continuous_apply 1).continuousAt.sub hminus))).add
      (hd.mul (continuousAt_const.sub hmv))
  · exact (hdv.mul (continuous_apply 2).continuousAt).add (hd.mul_const (Z 2))

theorem continuousAt_inversePowerQuadratic {r : ℝ} (hr : r ≠ 0)
    (m Z : Fin 3 → ℝ) (hm : 0 < m 0) (hdet : 0 < m 0 * m 1 - m 2 ^ 2)
    (hc : 0 < m 2) :
    ContinuousAt (fun n => symmetricTraceProduct Z
      (symmetricPowerVariation (1 / r) (symmetricPower r n) Z)) m := by
  obtain ⟨hminus, hplus⟩ := symmetricEigenvalues_positive hm hdet
  have hpower := (contDiffAt_symmetricPower (n := 0) r m hc.ne' hplus.ne' hminus.ne').continuousAt
  obtain ⟨hH0, _, hHdet⟩ := symmetricPower_positive_definite r m hm hdet hc.ne'
  have hHc : symmetricPower r m 2 ≠ 0 := by
    rcases lt_or_gt_of_ne hr with hr | hr
    · exact (symmetricPower_cross_negative hr m hm hdet hc).ne
    · exact (symmetricPower_cross_positive hr m hm hdet hc).ne'
  obtain ⟨hHminus, hHplus⟩ := symmetricEigenvalues_positive hH0 hHdet
  have hv := (continuousAt_symmetricPowerVariation (1 / r) (symmetricPower r m) Z
    hHc hHplus.ne' hHminus.ne').comp hpower
  have h0 := (continuous_apply 0).continuousAt.comp hv
  have h1 := (continuous_apply 1).continuousAt.comp hv
  have h2 := (continuous_apply 2).continuousAt.comp hv
  unfold symmetricTraceProduct
  exact ((h0.const_mul (Z 0)).add (h1.const_mul (Z 1))).add (h2.const_mul (2 * Z 2))

end

end ResearchMain.DiagonalSchatten
