import MainTheorems.WishartBlocks.SpectralLaw.LowerBartlettDensity
import MainTheorems.WishartBlocks.SpectralLaw.LowerIndexAlgebra
import Mathlib.Basic.ENNReal.BigOperators

namespace ResearchMain.WishartBlocks

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def lowerCoordinatePDFReal {n : ℕ} (α : ℝ)
    (e : LowerIndex n) (t : ℝ) : ℝ :=
  if e.val.1 = e.val.2 then
    if 0 < t then 2 * t * gammaPDFReal ((α - e.val.1.val) / 2) (1 / 2) (t ^ 2) else 0
  else gaussianPDFReal 0 1 t

noncomputable def lowerDensityCoefficient {n : ℕ} (α : ℝ) (e : LowerIndex n) : ℝ :=
  if e.val.1 = e.val.2 then
    (1 / 2 : ℝ) ^ ((α - e.val.1.val) / 2) / Real.Gamma ((α - e.val.1.val) / 2)
  else (Real.sqrt (2 * Real.pi))⁻¹

noncomputable def wishartDensityCoefficient (n : ℕ) (α : ℝ) : ℝ :=
  ∏ e : LowerIndex n, lowerDensityCoefficient α e

theorem bartlett_shape_positive {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (i : Fin n) : 0 < (α - i.val) / 2 := by
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  linarith

theorem lowerDensityCoefficient_pos {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (e : LowerIndex n) : 0 < lowerDensityCoefficient α e := by
  unfold lowerDensityCoefficient
  split_ifs
  · exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.Gamma_pos_of_pos (bartlett_shape_positive hα _))
  · exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))

theorem wishartDensityCoefficient_pos {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) : 0 < wishartDensityCoefficient n α :=
  Finset.prod_pos fun e _ => lowerDensityCoefficient_pos hα e

theorem lowerCoordinatePDFReal_nonneg {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) (e : LowerIndex n) (t : ℝ) :
    0 ≤ lowerCoordinatePDFReal α e t := by
  unfold lowerCoordinatePDFReal
  split_ifs with he ht
  · exact mul_nonneg (mul_nonneg (by norm_num) ht.le)
      (gammaPDFReal_nonneg (bartlett_shape_positive hα _) (by norm_num) _)
  · exact le_rfl
  · exact gaussianPDFReal_nonneg 0 1 t

theorem lowerCoordinatePDF_eq_ofReal {n : ℕ} {α : ℝ}
    (_hα : (n : ℝ) - 1 < α) (e : LowerIndex n) (t : ℝ) :
    lowerCoordinatePDF α e t = ENNReal.ofReal (lowerCoordinatePDFReal α e t) := by
  unfold lowerCoordinatePDF lowerCoordinatePDFReal
  split_ifs with he ht
  · unfold sqrtGammaPDF
    rw [ite_eq_left ht, gammaPDF,
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) ht.le)]
  · simp only [sqrtGammaPDF, ht, ite_false, ENNReal.ofReal_zero]
  · rfl

theorem lowerCoordinatePDFReal_positive_formula {n : ℕ} (α : ℝ)
    (e : LowerIndex n) {t : ℝ} (ht : e.val.1 = e.val.2 → 0 < t) :
    lowerCoordinatePDFReal α e t =
      lowerDensityCoefficient α e *
        (if e.val.1 = e.val.2 then 2 * t ^ (α - e.val.1.val - 1) else 1) *
        Real.exp (-(t ^ 2) / 2) := by
  unfold lowerCoordinatePDFReal lowerDensityCoefficient
  by_cases he : e.val.1 = e.val.2
  · simp only [← he, ite_true, ht he, gammaPDFReal, sq_nonneg]
    rw [← Real.rpow_natCast_mul (ht he).le 2]
    have hp : t * t ^ (2 * ((α - e.val.1.val) / 2 - 1)) =
        t ^ (α - e.val.1.val - 1) := by
      rw [show α - e.val.1.val - 1 = 1 + 2 * ((α - e.val.1.val) / 2 - 1) by ring_nf,
        Real.rpow_add (ht he), Real.rpow_one]
    rw [show -((1 / 2 : ℝ) * t ^ 2) = -(t ^ 2) / 2 by ring_nf]
    calc
      _ = ((1 / 2 : ℝ) ^ ((α - e.val.1.val) / 2) /
          Real.Gamma ((α - e.val.1.val) / 2)) *
          2 * (t * t ^ (2 * ((α - e.val.1.val) / 2 - 1))) *
          Real.exp (-(t ^ 2) / 2) := by ring_nf
      _ = _ := by rw [hp]; ring_nf
  · simp only [he, ite_false, gaussianPDFReal, NNReal.coe_one,
      mul_one, sub_zero]

theorem jacobian_det_power {n : ℕ} {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) (α : ℝ) :
    choleskyJacobianWeight x *
        (lowerMatrix x * (lowerMatrix x).transpose).det ^ ((α - n - 1) / 2) =
      2 ^ n * ∏ i : Fin n, lowerMatrix x i i ^ (α - i.val - 1) := by
  rw [choleskyJacobianWeight_formula, lowerGram_det_rpow hx, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast, ← Real.rpow_add (hx i)]
  congr 1
  rw [Nat.cast_sub i.isLt.le]
  ring_nf

theorem lowerBartlettPDF_cholesky {n : ℕ} {α : ℝ}
    (hα : (n : ℝ) - 1 < α) {x : LowerIndex n → ℝ}
    (hx : x ∈ positiveLowerCoordinates n) :
    lowerBartlettPDF α x = ENNReal.ofReal
      (choleskyJacobianWeight x * wishartDensityCoefficient n α *
        (lowerMatrix x * (lowerMatrix x).transpose).det ^ ((α - n - 1) / 2) *
        Real.exp (-(lowerMatrix x * (lowerMatrix x).transpose).trace / 2)) := by
  have ht (e : LowerIndex n) (he : e.val.1 = e.val.2) : 0 < x e := by
    rw [← lowerMatrix_entry x e, he]
    exact hx e.val.2
  unfold lowerBartlettPDF
  simp_rw [lowerCoordinatePDF_eq_ofReal hα]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => lowerCoordinatePDFReal_nonneg hα e _)]
  apply congrArg ENNReal.ofReal
  simp_rw [lowerCoordinatePDFReal_positive_formula α _ (ht _)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hdiag :
      (∏ e : LowerIndex n,
        if e.val.1 = e.val.2 then 2 * x e ^ (α - e.val.1.val - 1) else 1) =
        2 ^ n * ∏ i : Fin n, lowerMatrix x i i ^ (α - i.val - 1) := by
    have he (e : LowerIndex n) :
        (if e.val.1 = e.val.2 then 2 * x e ^ (α - e.val.1.val - 1) else 1) =
        (if e.val.1 = e.val.2 then
          2 * lowerMatrix x e.val.1 e.val.1 ^ (α - e.val.1.val - 1) else 1) := by
      split_ifs with hd
      · rw [← lowerMatrix_entry x e, hd]
      · rfl
    simp_rw [he]
    change (∏ e : LowerIndex n, if (ofLex e.val).1 = (ofLex e.val).2 then
      2 * lowerMatrix x (ofLex e.val).1 (ofLex e.val).1 ^
        (α - (ofLex e.val).1.val - 1) else 1) = _
    calc
      _ = ∏ i : Fin n, 2 * lowerMatrix x i i ^ (α - i.val - 1) :=
        lower_diagonal_product
          (fun i : Fin n => 2 * lowerMatrix x i i ^ (α - i.val - 1))
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hdiag, ← Real.exp_sum]
  have hexp : (∑ e : LowerIndex n, -(x e ^ 2) / 2) =
      -(lowerMatrix x * (lowerMatrix x).transpose).trace / 2 := by
    rw [lowerGram_trace, ← Finset.sum_neg_distrib, Finset.sum_div]
  rw [hexp, ← jacobian_det_power hx α]
  unfold wishartDensityCoefficient
  ring_nf

end ResearchMain.WishartBlocks
