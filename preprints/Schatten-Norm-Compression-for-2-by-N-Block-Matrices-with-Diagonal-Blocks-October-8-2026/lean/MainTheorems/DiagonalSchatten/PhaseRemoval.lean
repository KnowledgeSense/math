import MainTheorems.DiagonalSchatten.TwoRowSpectrum
import MainTheorems.DiagonalSchatten.EigenvaluePowerGap

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

def entrywiseAbs (W : Matrix (Fin 2) J ℂ) : Matrix (Fin 2) J ℂ :=
  fun i j => (‖W i j‖ : ℂ)

omit [DecidableEq J] in
theorem rowMass_entrywiseAbs (W : Matrix (Fin 2) J ℂ) (i : Fin 2) :
    rowMass (entrywiseAbs W) i = rowMass W i := by
  simp [rowMass, entrywiseAbs]

omit [DecidableEq J] in
theorem rowCross_entrywiseAbs (W : Matrix (Fin 2) J ℂ) :
    rowCross (entrywiseAbs W) = ((∑ j, ‖W 0 j‖ * ‖W 1 j‖ : ℝ) : ℂ) := by
  simp [rowCross, entrywiseAbs, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

omit [DecidableEq J] in
theorem rowCross_norm_entrywiseAbs (W : Matrix (Fin 2) J ℂ) :
    ‖rowCross (entrywiseAbs W)‖ = ∑ j, ‖W 0 j‖ * ‖W 1 j‖ := by
  rw [rowCross_entrywiseAbs, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))

omit [DecidableEq J] in
theorem rowCross_norm_le_entrywiseAbs (W : Matrix (Fin 2) J ℂ) :
    ‖rowCross W‖ ≤ ‖rowCross (entrywiseAbs W)‖ := by
  rw [rowCross_norm_entrywiseAbs]
  exact rowCross_norm_le W

omit [DecidableEq J] in
theorem twoEigenvalueGap_row_bound (W : Matrix (Fin 2) J ℂ) :
    twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross W) ≤
      rowMass W 0 + rowMass W 1 := by
  have h := twoEigenvalueMinus_nonneg (rowCross W)
    (rowMass_nonneg W 0) (rowMass_nonneg W 1) (rowCross_sq_le W)
  unfold twoEigenvalueMinus at h
  linarith

omit [DecidableEq J] in
theorem twoEigenvalueGap_phase_le (W : Matrix (Fin 2) J ℂ) :
    twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross W) ≤
      twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross (entrywiseAbs W)) := by
  have h := rowCross_norm_le_entrywiseAbs W
  have hn := norm_nonneg (rowCross W)
  have hm := norm_nonneg (rowCross (entrywiseAbs W))
  unfold twoEigenvalueGap
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem schattenPower_twoRow_gap {p : ℝ} (hp : 0 < p) (W : Matrix (Fin 2) J ℂ) :
    schattenPower p W = eigenvaluePowerGap (p / 2) (rowMass W 0 + rowMass W 1)
      (twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross W)) := by
  rw [schattenPower_twoRow hp]
  rfl

theorem phaseRemoval_power_upper {p : ℝ} (hp : 2 ≤ p) (W : Matrix (Fin 2) J ℂ) :
    schattenPower p W ≤ schattenPower p (entrywiseAbs W) := by
  have hp0 : 0 < p := by linarith
  rw [schattenPower_twoRow_gap hp0, schattenPower_twoRow_gap hp0,
    rowMass_entrywiseAbs, rowMass_entrywiseAbs]
  have hboundAbs :
      twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross (entrywiseAbs W)) ≤
        rowMass W 0 + rowMass W 1 := by
    simpa only [rowMass_entrywiseAbs] using twoEigenvalueGap_row_bound (entrywiseAbs W)
  exact eigenvaluePowerGap_monotone (q := p / 2) (by linarith)
    ⟨Real.sqrt_nonneg _, twoEigenvalueGap_row_bound W⟩
    ⟨Real.sqrt_nonneg _, hboundAbs⟩ (twoEigenvalueGap_phase_le W)

theorem phaseRemoval_power_lower {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (W : Matrix (Fin 2) J ℂ) :
    schattenPower p (entrywiseAbs W) ≤ schattenPower p W := by
  rw [schattenPower_twoRow_gap hp, schattenPower_twoRow_gap hp,
    rowMass_entrywiseAbs, rowMass_entrywiseAbs]
  have hboundAbs :
      twoEigenvalueGap (rowMass W 0) (rowMass W 1) (rowCross (entrywiseAbs W)) ≤
        rowMass W 0 + rowMass W 1 := by
    simpa only [rowMass_entrywiseAbs] using twoEigenvalueGap_row_bound (entrywiseAbs W)
  exact eigenvaluePowerGap_antitone (q := p / 2) (by linarith) (by linarith)
    ⟨Real.sqrt_nonneg _, twoEigenvalueGap_row_bound W⟩
    ⟨Real.sqrt_nonneg _, hboundAbs⟩ (twoEigenvalueGap_phase_le W)

theorem phaseRemoval_upper {p : ℝ} (hp : 2 ≤ p) (W : Matrix (Fin 2) J ℂ) :
    schattenNorm p W ≤ schattenNorm p (entrywiseAbs W) := by
  have hp0 : 0 < p := by linarith
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p W) (phaseRemoval_power_upper hp W)
    (one_div_nonneg.mpr hp0.le)

theorem phaseRemoval_lower {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (W : Matrix (Fin 2) J ℂ) :
    schattenNorm p (entrywiseAbs W) ≤ schattenNorm p W := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p (entrywiseAbs W))
    (phaseRemoval_power_lower hp hp2 W) (one_div_nonneg.mpr hp.le)

end

end ResearchMain.DiagonalSchatten
