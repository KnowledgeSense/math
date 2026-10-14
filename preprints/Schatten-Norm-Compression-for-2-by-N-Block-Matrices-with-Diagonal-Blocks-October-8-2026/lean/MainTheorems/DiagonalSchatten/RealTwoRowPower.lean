import MainTheorems.DiagonalSchatten.TwoRowSpectrum
import MainTheorems.DiagonalSchatten.AreaVector
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def complexifyRows (X : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℂ :=
  fun i j => (X i j : ℂ)

def realGramPlus (X : Matrix (Fin 2) J ℝ) : ℝ :=
  (gramFirst X + gramSecond X +
    Real.sqrt ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2)) / 2

def realGramMinus (X : Matrix (Fin 2) J ℝ) : ℝ :=
  (gramFirst X + gramSecond X -
    Real.sqrt ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2)) / 2

theorem rowMass_complexify (X : Matrix (Fin 2) J ℝ) (i : Fin 2) :
    rowMass (complexifyRows X) i = ∑ j, X i j ^ 2 := by
  simp [rowMass, complexifyRows, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem rowCross_complexify (X : Matrix (Fin 2) J ℝ) :
    rowCross (complexifyRows X) = (gramCross X : ℂ) := by
  simp [rowCross, complexifyRows, gramCross, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

theorem realGramPlus_eq (X : Matrix (Fin 2) J ℝ) :
    realGramPlus X = twoEigenvaluePlus (gramFirst X) (gramSecond X) (gramCross X : ℂ) := by
  simp [realGramPlus, twoEigenvaluePlus, twoEigenvalueGap,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem realGramMinus_eq (X : Matrix (Fin 2) J ℝ) :
    realGramMinus X = twoEigenvalueMinus (gramFirst X) (gramSecond X) (gramCross X : ℂ) := by
  simp [realGramMinus, twoEigenvalueMinus, twoEigenvalueGap,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem realGram_nonneg (X : Matrix (Fin 2) J ℝ) :
    0 ≤ realGramPlus X ∧ 0 ≤ realGramMinus X := by
  have ha : 0 ≤ gramFirst X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ gramSecond X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := rowCross_sq_le (complexifyRows X)
  rw [rowCross_complexify, rowMass_complexify, rowMass_complexify] at hcs
  rw [realGramPlus_eq, realGramMinus_eq]
  exact ⟨twoEigenvaluePlus_nonneg _ ha hb, twoEigenvalueMinus_nonneg _ ha hb hcs⟩

theorem areaVector_norm_sq_eq_eigenvalues (X : Matrix (Fin 2) J ℝ) :
    ‖areaVector X‖ ^ 2 = 2 * (realGramPlus X * realGramMinus X) := by
  rw [areaVector_norm_sq, realGramPlus_eq, realGramMinus_eq, twoEigenvalues_product]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

variable [DecidableEq J]

theorem schattenPower_complexify {p : ℝ} (hp : 0 < p) (X : Matrix (Fin 2) J ℝ) :
    schattenPower p (complexifyRows X) =
      realGramPlus X ^ (p / 2) + realGramMinus X ^ (p / 2) := by
  rw [schattenPower_twoRow hp, rowMass_complexify, rowMass_complexify,
    rowCross_complexify, realGramPlus_eq, realGramMinus_eq]
  rfl

theorem schattenPower_complexify_area {p : ℝ} (hp : 0 < p)
    (X : Matrix (Fin 2) J ℝ) :
    schattenPower p (complexifyRows X) = realGramPlus X ^ (p / 2) +
      ‖areaVector X‖ ^ p * (2 * realGramPlus X) ^ (-(p / 2)) := by
  rw [schattenPower_complexify hp]
  have hn := realGram_nonneg X
  have harea := areaVector_norm_sq_eq_eigenvalues X
  by_cases hz : realGramPlus X = 0
  · have hm : realGramMinus X = 0 := by
      have hgap := Real.sqrt_nonneg
        ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2)
      have hmnonneg := hn.2
      unfold realGramPlus at hz
      unfold realGramMinus at hmnonneg ⊢
      linarith
    have har : ‖areaVector X‖ = 0 := by rw [hz] at harea; nlinarith [norm_nonneg (areaVector X)]
    simp [hz, hm, har, Real.zero_rpow hp.ne', Real.zero_rpow (by linarith : p / 2 ≠ 0)]
  · have hplus : 0 < realGramPlus X := lt_of_le_of_ne hn.1 (Ne.symm hz)
    have hm : realGramMinus X = ‖areaVector X‖ ^ 2 / (2 * realGramPlus X) := by
      apply (eq_div_iff (by positivity : 2 * realGramPlus X ≠ 0)).mpr
      nlinarith
    rw [hm, Real.div_rpow (sq_nonneg _) (by positivity)]
    have hpow : (‖areaVector X‖ ^ 2) ^ (p / 2) = ‖areaVector X‖ ^ p := by
      rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
      congr 1
      ring
    rw [hpow, Real.rpow_neg (by positivity)]
    rfl

omit [DecidableEq J] in
theorem contDiffAt_realGramPlus {n : WithTop ℕ∞} (X : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    ContDiffAt ℝ n realGramPlus X := by
  have hpoly : ContDiff ℝ n (fun Y : Matrix (Fin 2) J ℝ =>
      (gramFirst Y - gramSecond Y) ^ 2 + 4 * gramCross Y ^ 2) := by
    unfold gramFirst gramSecond gramCross
    fun_prop
  have hpos : 0 < (gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hc, sq_nonneg (gramFirst X - gramSecond X)]
  have hs := hpoly.contDiffAt.sqrt hpos.ne'
  unfold realGramPlus
  exact (((by unfold gramFirst gramSecond; fun_prop) :
      ContDiffAt ℝ n (fun Y : Matrix (Fin 2) J ℝ => gramFirst Y + gramSecond Y) X).add hs).div_const 2

omit [DecidableEq J] in
theorem contDiffAt_realGramMinus {n : WithTop ℕ∞} (X : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0) :
    ContDiffAt ℝ n realGramMinus X := by
  have heq : realGramMinus (J := J) =
      (fun Y => gramFirst Y + gramSecond Y - realGramPlus Y) := by
    funext Y
    unfold realGramMinus realGramPlus
    ring
  rw [heq]
  exact (((by unfold gramFirst gramSecond; fun_prop) :
    ContDiffAt ℝ n (fun Y : Matrix (Fin 2) J ℝ => gramFirst Y + gramSecond Y) X).sub
      (contDiffAt_realGramPlus X hc))

omit [DecidableEq J] in
theorem realGram_product (X : Matrix (Fin 2) J ℝ) :
    realGramPlus X * realGramMinus X = gramFirst X * gramSecond X - gramCross X ^ 2 := by
  rw [realGramPlus_eq, realGramMinus_eq, twoEigenvalues_product]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

omit [DecidableEq J] in
theorem realGram_eigenvalues_positive (X : Matrix (Fin 2) J ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    0 < realGramPlus X ∧ 0 < realGramMinus X := by
  have hpos : 0 < realGramPlus X * realGramMinus X := by rw [realGram_product]; exact hdet
  have hn := realGram_nonneg X
  constructor
  · by_contra h
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hn.2
    linarith
  · by_contra h
    have hprod := mul_nonpos_of_nonneg_of_nonpos hn.1 (le_of_not_gt h)
    linarith

theorem contDiffAt_schattenPower_complexify_fullRank {n : WithTop ℕ∞} {p : ℝ} (hp : 0 < p)
    (X : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) :
    ContDiffAt ℝ n (fun Y : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows Y)) X := by
  have heq : (fun Y : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows Y)) =
      (fun Y => realGramPlus Y ^ (p / 2) + realGramMinus Y ^ (p / 2)) :=
    funext (schattenPower_complexify hp)
  rw [heq]
  have hn := realGram_eigenvalues_positive X hdet
  exact ((contDiffAt_realGramPlus X hc).rpow_const_of_ne hn.1.ne').add
    ((contDiffAt_realGramMinus X hc).rpow_const_of_ne hn.2.ne')

theorem contDiffAt_schattenPower_complexify {p : ℝ} (hp : 1 < p)
    (X : Matrix (Fin 2) J ℝ) (hc : gramCross X ≠ 0)
    (htrace : 0 < gramFirst X + gramSecond X) :
    ContDiffAt ℝ 1 (fun Y : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows Y)) X := by
  have hplus : 0 < realGramPlus X := by
    unfold realGramPlus
    have hs := Real.sqrt_nonneg
      ((gramFirst X - gramSecond X) ^ 2 + 4 * gramCross X ^ 2)
    linarith
  have hdiff : ContDiffAt ℝ 1 realGramPlus X := contDiffAt_realGramPlus X hc
  have hden : ContDiffAt ℝ 1 (fun Y => 2 * realGramPlus Y) X := contDiffAt_const.mul hdiff
  have hformula : ContDiffAt ℝ 1 (fun Y : Matrix (Fin 2) J ℝ =>
      realGramPlus Y ^ (p / 2) + ‖areaVector Y‖ ^ p * (2 * realGramPlus Y) ^ (-(p / 2))) X :=
    (hdiff.rpow_const_of_ne hplus.ne').add
      ((contDiff_areaVector_norm_rpow hp).contDiffAt.mul
        (hden.rpow_const_of_ne (by positivity)))
  exact hformula.congr_of_eventuallyEq (Filter.Eventually.of_forall fun Y =>
    schattenPower_complexify_area (by linarith) Y)

end

end ResearchMain.DiagonalSchatten
