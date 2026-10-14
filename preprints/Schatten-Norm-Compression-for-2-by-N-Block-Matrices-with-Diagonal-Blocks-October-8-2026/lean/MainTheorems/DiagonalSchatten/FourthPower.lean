import MainTheorems.DiagonalSchatten.CompressionFunctional
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
theorem schattenPower_four_twoRow (W : Matrix (Fin 2) J ℂ) :
    schattenPower 4 W = rowMass W 0 ^ 2 + rowMass W 1 ^ 2 + 2 * ‖rowCross W‖ ^ 2 := by
  rw [schattenPower_twoRow (by norm_num : (0 : ℝ) < 4)]
  norm_num only [show (4 : ℝ) / 2 = 2 by norm_num, Real.rpow_two]
  have hs := twoEigenvalues_sum (rowMass W 0) (rowMass W 1) (rowCross W)
  have hp := twoEigenvalues_product (rowMass W 0) (rowMass W 1) (rowCross W)
  have hsq := congrArg (fun x : ℝ => x ^ 2) hs
  nlinarith [hsq]

omit [DecidableEq J] [DecidableEq D] in
theorem finite_minkowski_sq (f : J → D → ℝ) :
    (∑ d, (∑ j, f j d) ^ 2) ≤ (∑ j, Real.sqrt (∑ d, f j d ^ 2)) ^ 2 := by
  let v : J → EuclideanSpace ℝ D := fun j => WithLp.toLp 2 (f j)
  have hn : ‖∑ j, v j‖ ≤ ∑ j, ‖v j‖ := norm_sum_le _ _
  have hl : ‖∑ j, v j‖ ^ 2 = ∑ d, (∑ j, f j d) ^ 2 := by
    change ‖∑ j, WithLp.toLp 2 (f j)‖ ^ 2 = _
    rw [← WithLp.toLp_sum, EuclideanSpace.real_norm_sq_eq]
    simp only [Finset.sum_apply]
  have hr : (∑ j, ‖v j‖) = ∑ j, Real.sqrt (∑ d, f j d ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [v, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have hleft := norm_nonneg (∑ j, v j)
  have hright : 0 ≤ ∑ j, ‖v j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (v j))
  rw [← hl, ← hr]
  nlinarith

theorem diagonal_norm_four_power (v : D → ℂ) :
    schattenNorm 4 (Matrix.diagonal v) ^ 4 = ∑ d, ‖v d‖ ^ 4 := by
  have h := schattenNorm_rpow 4 (by norm_num) (Matrix.diagonal v)
  rw [Real.rpow_ofNat] at h
  rw [h, schattenPower_diagonal]
  simp only [Real.rpow_ofNat]

theorem diagonal_norm_four_sq (v : D → ℂ) :
    schattenNorm 4 (Matrix.diagonal v) ^ 2 = Real.sqrt (∑ d, ‖v d‖ ^ 4) := by
  have h := diagonal_norm_four_power v
  have hsq : (schattenNorm 4 (Matrix.diagonal v) ^ 2) ^ 2 = ∑ d, ‖v d‖ ^ 4 := by
    nlinarith
  rw [← hsq, Real.sqrt_sq (sq_nonneg _)]

omit [DecidableEq J] in
theorem rowMass_compression_four (z : Fin 2 → J → D → ℂ) (i : Fin 2) :
    rowMass (compression 4 z) i =
      ∑ j, Real.sqrt (∑ d, ‖z i j d‖ ^ 4) := by
  unfold rowMass
  apply Finset.sum_congr rfl
  intro j _
  rw [compression, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (schattenNorm_nonneg 4 (diagonalBlock z i j))]
  exact diagonal_norm_four_sq (z i j)

omit [DecidableEq J] in
theorem rowMass_four_bound (z : Fin 2 → J → D → ℂ) (i : Fin 2) :
    (∑ d, (∑ j, ‖z i j d‖ ^ 2) ^ 2) ≤ rowMass (compression 4 z) i ^ 2 := by
  rw [rowMass_compression_four]
  have h := finite_minkowski_sq (fun j d => ‖z i j d‖ ^ 2)
  simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using h

theorem fourth_product_bound (v w : D → ℂ) :
    Real.sqrt (∑ d, (‖v d‖ * ‖w d‖) ^ 2) ≤
      schattenNorm 4 (Matrix.diagonal v) * schattenNorm 4 (Matrix.diagonal w) := by
  let h := Real.sqrt (∑ d, (‖v d‖ * ‖w d‖) ^ 2)
  let r := schattenNorm 4 (Matrix.diagonal v) * schattenNorm 4 (Matrix.diagonal w)
  have hh : 0 ≤ h := Real.sqrt_nonneg _
  have hr : 0 ≤ r := mul_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _)
  have hs : h ^ 2 = ∑ d, ‖v d‖ ^ 2 * ‖w d‖ ^ 2 := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset D)
    (fun d => ‖v d‖ ^ 2) (fun d => ‖w d‖ ^ 2)
  have hpow : h ^ 4 ≤ r ^ 4 := by
    change h ^ 4 ≤ (schattenNorm 4 (Matrix.diagonal v) *
      schattenNorm 4 (Matrix.diagonal w)) ^ 4
    rw [mul_pow, diagonal_norm_four_power, diagonal_norm_four_power]
    have hid : h ^ 4 = (∑ d, ‖v d‖ ^ 2 * ‖w d‖ ^ 2) ^ 2 := by rw [← hs]; ring
    rw [hid]
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hcs
  exact (pow_le_pow_iff_left₀ hh hr (by decide : (4 : ℕ) ≠ 0)).mp hpow

omit [DecidableEq J] in
theorem rowCross_norm_compression (p : ℝ) (z : Fin 2 → J → D → ℂ) :
    ‖rowCross (compression p z)‖ =
      ∑ j, schattenNorm p (Matrix.diagonal (z 0 j)) *
        schattenNorm p (Matrix.diagonal (z 1 j)) := by
  have hr : rowCross (compression p z) =
      ((∑ j, schattenNorm p (Matrix.diagonal (z 0 j)) *
        schattenNorm p (Matrix.diagonal (z 1 j)) : ℝ) : ℂ) := by
    simp [rowCross, compression, diagonalBlock, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [hr, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _))

omit [DecidableEq J] in
theorem rowCross_four_bound (z : Fin 2 → J → D → ℂ) :
    (∑ d, ‖rowCross (fun i j => z i j d : Matrix (Fin 2) J ℂ)‖ ^ 2) ≤
      ‖rowCross (compression 4 z)‖ ^ 2 := by
  rw [rowCross_norm_compression]
  calc
    _ ≤ ∑ d, (∑ j, ‖z 0 j d‖ * ‖z 1 j d‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro d _
      have h := rowCross_norm_le (fun i j => z i j d : Matrix (Fin 2) J ℂ)
      have hn := norm_nonneg (rowCross (fun i j => z i j d : Matrix (Fin 2) J ℂ))
      have hs : 0 ≤ ∑ j, ‖z 0 j d‖ * ‖z 1 j d‖ :=
        Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith
    _ ≤ (∑ j, Real.sqrt (∑ d, (‖z 0 j d‖ * ‖z 1 j d‖) ^ 2)) ^ 2 :=
      finite_minkowski_sq _
    _ ≤ _ := by
      have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
        fourth_product_bound (z 0 j) (z 1 j)
      have hleft : 0 ≤ ∑ j, Real.sqrt (∑ d, (‖z 0 j d‖ * ‖z 1 j d‖) ^ 2) :=
        Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
      have hright : 0 ≤ ∑ j, schattenNorm 4 (Matrix.diagonal (z 0 j)) *
          schattenNorm 4 (Matrix.diagonal (z 1 j)) :=
        Finset.sum_nonneg fun _ _ =>
          mul_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _)
      nlinarith

theorem diagonal_compression_four_power (z : Fin 2 → J → D → ℂ) :
    schattenPower 4 (diagonalBlockMatrix z) ≤ schattenPower 4 (compression 4 z) := by
  have hexp : schattenPower 4 (diagonalBlockMatrix z) =
      ∑ d, (rowMass (Matrix.of fun i j => z i j d) 0 ^ 2 +
        rowMass (Matrix.of fun i j => z i j d) 1 ^ 2 +
        2 * ‖rowCross (Matrix.of fun i j => z i j d)‖ ^ 2) := by
    rw [diagonalBlockMatrix_schattenPower]
    exact Finset.sum_congr rfl fun d _ => schattenPower_four_twoRow (Matrix.of fun i j => z i j d)
  rw [hexp, schattenPower_four_twoRow]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have ha := rowMass_four_bound z 0
  have hb := rowMass_four_bound z 1
  have hc := rowCross_four_bound z
  change (∑ d, ‖rowCross (Matrix.of fun i j => z i j d)‖ ^ 2) ≤
    ‖rowCross (compression 4 z)‖ ^ 2 at hc
  change (∑ d, (∑ j, ‖z 0 j d‖ ^ 2) ^ 2) +
    (∑ d, (∑ j, ‖z 1 j d‖ ^ 2) ^ 2) +
    2 * (∑ d, ‖rowCross (Matrix.of fun i j => z i j d)‖ ^ 2) ≤ _
  linarith

theorem diagonal_compression_four (z : Fin 2 → J → D → ℂ) :
    schattenNorm 4 (diagonalBlockMatrix z) ≤ schattenNorm 4 (compression 4 z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg _ _)
    (diagonal_compression_four_power z) (by norm_num)

end

end ResearchMain.DiagonalSchatten
