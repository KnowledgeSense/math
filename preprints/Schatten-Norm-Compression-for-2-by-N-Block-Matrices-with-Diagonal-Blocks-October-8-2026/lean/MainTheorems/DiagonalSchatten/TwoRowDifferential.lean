import MainTheorems.DiagonalSchatten.RealTwoRowPower
import MainTheorems.DiagonalSchatten.GramDifferential

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def realGramGap (X : Matrix (Fin 2) J ℝ) : ℝ :=
  Real.sqrt ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2)

theorem realGramGap_positive (X : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    0 < realGramGap X := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (gramFirst X - gramSecond X), sq_pos_of_ne_zero hc]

theorem realGramGap_direction_deriv (X Y : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    HasDerivAt (fun t : ℝ => realGramGap (rowDirection X Y t))
      (((gramFirst X - gramSecond X) *
          (fderiv ℝ gramFirst X Y - fderiv ℝ gramSecond X Y) +
        4 * gramCross X * fderiv ℝ gramCross X Y) / realGramGap X) 0 := by
  have ha := gramFirst_direction_deriv X Y
  have hb := gramSecond_direction_deriv X Y
  have hc' := gramCross_direction_deriv X Y
  rw [← fderiv_gramFirst X Y] at ha
  rw [← fderiv_gramSecond X Y] at hb
  rw [← fderiv_gramCross X Y] at hc'
  have hD : HasDerivAt (fun t : ℝ =>
      (gramFirst (rowDirection X Y t) - gramSecond (rowDirection X Y t)) ^ 2 +
        4 * gramCross (rowDirection X Y t) ^ 2)
      (2 * (gramFirst X - gramSecond X) *
          (fderiv ℝ gramFirst X Y - fderiv ℝ gramSecond X Y) +
        8 * gramCross X * fderiv ℝ gramCross X Y) 0 := by
    convert! ((ha.sub hb).fun_pow 2).add ((hc'.fun_pow 2).const_mul 4) using 1
    simp only [Pi.sub_apply, rowDirection_zero]
    ring
  have hDn : (gramFirst (rowDirection X Y 0) - gramSecond (rowDirection X Y 0)) ^ 2 +
      4 * gramCross (rowDirection X Y 0) ^ 2 ≠ 0 := by
    rw [rowDirection_zero]
    have hp : 0 < (gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2 := by
      nlinarith [sq_nonneg (gramFirst X - gramSecond X), sq_pos_of_ne_zero hc]
    exact hp.ne'
  convert! hD.sqrt hDn using 1
  simp only [rowDirection_zero]
  have hgap := (realGramGap_positive X hc).ne'
  dsimp [realGramGap] at hgap
  unfold realGramGap
  field_simp [hgap]
  ring

theorem realGramPlus_direction_deriv (X Y : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    HasDerivAt (fun t : ℝ => realGramPlus (rowDirection X Y t))
      ((fderiv ℝ gramFirst X Y + fderiv ℝ gramSecond X Y +
        ((gramFirst X - gramSecond X) *
            (fderiv ℝ gramFirst X Y - fderiv ℝ gramSecond X Y) +
          4 * gramCross X * fderiv ℝ gramCross X Y) / realGramGap X) / 2) 0 := by
  have ha := gramFirst_direction_deriv X Y
  have hb := gramSecond_direction_deriv X Y
  rw [← fderiv_gramFirst X Y] at ha
  rw [← fderiv_gramSecond X Y] at hb
  exact ((ha.add hb).add (realGramGap_direction_deriv X Y hc)).div_const 2

theorem realGramMinus_direction_deriv (X Y : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    HasDerivAt (fun t : ℝ => realGramMinus (rowDirection X Y t))
      ((fderiv ℝ gramFirst X Y + fderiv ℝ gramSecond X Y -
        ((gramFirst X - gramSecond X) *
            (fderiv ℝ gramFirst X Y - fderiv ℝ gramSecond X Y) +
          4 * gramCross X * fderiv ℝ gramCross X Y) / realGramGap X) / 2) 0 := by
  have ha := gramFirst_direction_deriv X Y
  have hb := gramSecond_direction_deriv X Y
  rw [← fderiv_gramFirst X Y] at ha
  rw [← fderiv_gramSecond X Y] at hb
  exact ((ha.add hb).sub (realGramGap_direction_deriv X Y hc)).div_const 2

def realGramPowerCoefficient (r : ℝ) (X : Matrix (Fin 2) J ℝ) : Fin 3 → ℝ :=
  let d := (realGramPlus X ^ r - realGramMinus X ^ r) / realGramGap X
  ![realGramMinus X ^ r + d * (gramFirst X - realGramMinus X),
    realGramMinus X ^ r + d * (gramSecond X - realGramMinus X), d * gramCross X]

variable [DecidableEq J]

theorem schattenPower_complexify_direction_deriv {p : ℝ} (hp : 0 < p)
    (X Y : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    HasDerivAt (fun t : ℝ => schattenPower p (complexifyRows (rowDirection X Y t)))
      ((p / 2) * (realGramPowerCoefficient ((p - 2) / 2) X 0 * fderiv ℝ gramFirst X Y +
        realGramPowerCoefficient ((p - 2) / 2) X 1 * fderiv ℝ gramSecond X Y +
        2 * realGramPowerCoefficient ((p - 2) / 2) X 2 * fderiv ℝ gramCross X Y)) 0 := by
  have hEigen := realGram_eigenvalues_positive X hdet
  have hplus := (realGramPlus_direction_deriv X Y hc).rpow_const (p := p / 2)
    (Or.inl (by rw [rowDirection_zero]; exact hEigen.1.ne'))
  have hminus := (realGramMinus_direction_deriv X Y hc).rpow_const (p := p / 2)
    (Or.inl (by rw [rowDirection_zero]; exact hEigen.2.ne'))
  have heq : (fun t : ℝ => schattenPower p (complexifyRows (rowDirection X Y t))) =
      (fun t => realGramPlus (rowDirection X Y t) ^ (p / 2) +
        realGramMinus (rowDirection X Y t) ^ (p / 2)) :=
    funext fun t => schattenPower_complexify hp _
  rw [heq]
  convert! hplus.add hminus using 1
  simp only [rowDirection_zero]
  rw [show p / 2 - 1 = (p - 2) / 2 by ring]
  simp [realGramPowerCoefficient]
  have hgap := (realGramGap_positive X hc).ne'
  have he : realGramMinus X = (gramFirst X + gramSecond X - realGramGap X) / 2 := rfl
  rw [he]
  field_simp [hgap]
  ring

theorem fderiv_schattenPower_complexify {p : ℝ} (hp : 0 < p)
    (X Y : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    fderiv ℝ (fun Z : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows Z)) X Y =
      (p / 2) * (realGramPowerCoefficient ((p - 2) / 2) X 0 * fderiv ℝ gramFirst X Y +
        realGramPowerCoefficient ((p - 2) / 2) X 1 * fderiv ℝ gramSecond X Y +
        2 * realGramPowerCoefficient ((p - 2) / 2) X 2 * fderiv ℝ gramCross X Y) := by
  have hd := (contDiffAt_schattenPower_complexify_fullRank (n := 1) hp X hc hdet).differentiableAt
    (by norm_num)
  have he := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (rowDirection_hasDerivAt X Y)
    (rowDirection_zero X Y).symm
  exact he.unique (schattenPower_complexify_direction_deriv hp X Y hc hdet)

end

end ResearchMain.DiagonalSchatten
