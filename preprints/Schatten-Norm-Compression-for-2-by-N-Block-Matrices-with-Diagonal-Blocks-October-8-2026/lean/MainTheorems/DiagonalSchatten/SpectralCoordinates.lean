import MainTheorems.DiagonalSchatten.CompressionSecondVariation
import MainTheorems.DiagonalSchatten.WeightedDuality

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def spectralCoordinates (theta q : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![theta * z 0 + (1 - theta) * z 1 + 2 * q * z 2,
    (1 - theta) * z 0 + theta * z 1 - 2 * q * z 2,
    q * (z 1 - z 0) + (2 * theta - 1) * z 2]

def fromSpectralCoordinates (theta q : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![theta * z 0 + (1 - theta) * z 1 - 2 * q * z 2,
    (1 - theta) * z 0 + theta * z 1 + 2 * q * z 2,
    q * (z 0 - z 1) + (2 * theta - 1) * z 2]

theorem fromSpectralCoordinates_left_inverse {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (z : Fin 3 → ℝ) :
    fromSpectralCoordinates theta q (spectralCoordinates theta q z) = z := by
  funext i
  fin_cases i <;> simp [fromSpectralCoordinates, spectralCoordinates]
  · linear_combination 2 * (z 0 - z 1) * hq
  · linear_combination 2 * (z 1 - z 0) * hq
  · linear_combination 4 * z 2 * hq

theorem fromSpectralCoordinates_right_inverse {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (z : Fin 3 → ℝ) :
    spectralCoordinates theta q (fromSpectralCoordinates theta q z) = z := by
  funext i
  fin_cases i <;> simp [fromSpectralCoordinates, spectralCoordinates]
  · linear_combination 2 * (z 0 - z 1) * hq
  · linear_combination 2 * (z 1 - z 0) * hq
  · linear_combination 4 * z 2 * hq

theorem spectralCoordinates_trace_product {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (z w : Fin 3 → ℝ) :
    symmetricTraceProduct (spectralCoordinates theta q z) (spectralCoordinates theta q w) =
      symmetricTraceProduct z w := by
  unfold symmetricTraceProduct spectralCoordinates
  simp
  linear_combination 2 * ((z 0 - z 1) * (w 0 - w 1) + 4 * z 2 * w 2) * hq

def spectralWeightedMap (theta q : ℝ) (weights z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fromSpectralCoordinates theta q (weights * spectralCoordinates theta q z)

theorem spectralWeightedMap_trace_pair {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z w : Fin 3 → ℝ) :
    symmetricTraceProduct z (spectralWeightedMap theta q weights w) =
      weights 0 * spectralCoordinates theta q z 0 * spectralCoordinates theta q w 0 +
        weights 1 * spectralCoordinates theta q z 1 * spectralCoordinates theta q w 1 +
        2 * weights 2 * spectralCoordinates theta q z 2 * spectralCoordinates theta q w 2 := by
  rw [← spectralCoordinates_trace_product hq z (spectralWeightedMap theta q weights w)]
  rw [spectralWeightedMap, fromSpectralCoordinates_right_inverse hq]
  unfold symmetricTraceProduct
  simp only [Pi.mul_apply]
  ring

theorem spectralWeightedMap_trace_symmetric {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z w : Fin 3 → ℝ) :
    symmetricTraceProduct z (spectralWeightedMap theta q weights w) =
      symmetricTraceProduct w (spectralWeightedMap theta q weights z) := by
  rw [spectralWeightedMap_trace_pair hq, spectralWeightedMap_trace_pair hq]
  ring

theorem spectralWeightedMap_add (theta q : ℝ) (weights z w : Fin 3 → ℝ) :
    spectralWeightedMap theta q weights (z + w) =
      spectralWeightedMap theta q weights z + spectralWeightedMap theta q weights w := by
  funext i
  fin_cases i <;>
    simp [spectralWeightedMap, fromSpectralCoordinates, spectralCoordinates] <;> ring

theorem spectralWeightedMap_smul (theta q t : ℝ) (weights z : Fin 3 → ℝ) :
    spectralWeightedMap theta q weights (t • z) = t • spectralWeightedMap theta q weights z := by
  funext i
  fin_cases i <;>
    simp [spectralWeightedMap, fromSpectralCoordinates, spectralCoordinates, smul_eq_mul] <;> ring

theorem spectralWeightedMap_trace {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z : Fin 3 → ℝ) :
    symmetricTraceProduct z (spectralWeightedMap theta q weights z) =
      weights 0 * (spectralCoordinates theta q z 0) ^ 2 +
        weights 1 * (spectralCoordinates theta q z 1) ^ 2 +
        2 * weights 2 * (spectralCoordinates theta q z 2) ^ 2 := by
  rw [← spectralCoordinates_trace_product hq z
      (spectralWeightedMap theta q weights z)]
  rw [spectralWeightedMap, fromSpectralCoordinates_right_inverse hq]
  unfold symmetricTraceProduct
  simp only [Pi.mul_apply]
  ring

theorem spectralWeightedMap_inverse {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z : Fin 3 → ℝ)
    (hw : ∀ i, weights i ≠ 0) :
    spectralWeightedMap theta q (fun i => (weights i)⁻¹)
      (spectralWeightedMap theta q weights z) = z := by
  unfold spectralWeightedMap
  rw [fromSpectralCoordinates_right_inverse hq]
  have he : (fun i => (weights i)⁻¹) * (weights * spectralCoordinates theta q z) =
      spectralCoordinates theta q z := by
    funext i
    simp only [Pi.mul_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (hw i), one_mul]
  rw [he, fromSpectralCoordinates_left_inverse hq]

theorem spectralWeightedMap_neg (theta q : ℝ) (weights z : Fin 3 → ℝ) :
    spectralWeightedMap theta q (-weights) z = -spectralWeightedMap theta q weights z := by
  funext i
  fin_cases i <;>
    simp [spectralWeightedMap, fromSpectralCoordinates, spectralCoordinates] <;> ring

theorem spectralWeightedMap_trace_nonnegative {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ weights i) :
    0 ≤ symmetricTraceProduct z (spectralWeightedMap theta q weights z) := by
  rw [spectralWeightedMap_trace hq]
  exact add_nonneg
    (add_nonneg (mul_nonneg (hw 0) (sq_nonneg _)) (mul_nonneg (hw 1) (sq_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num) (hw 2)) (sq_nonneg _))

theorem spectralWeightedMap_trace_nonpositive {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z : Fin 3 → ℝ)
    (hw : ∀ i, weights i ≤ 0) :
    symmetricTraceProduct z (spectralWeightedMap theta q weights z) ≤ 0 := by
  rw [spectralWeightedMap_trace hq]
  exact add_nonpos
    (add_nonpos (mul_nonpos_of_nonpos_of_nonneg (hw 0) (sq_nonneg _))
      (mul_nonpos_of_nonpos_of_nonneg (hw 1) (sq_nonneg _)))
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hw 2))
      (sq_nonneg _))

theorem spectralWeightedMap_cauchy {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z w : Fin 3 → ℝ)
    (hw : ∀ i, 0 < weights i) :
    symmetricTraceProduct z w ^ 2 ≤
      symmetricTraceProduct z (spectralWeightedMap theta q weights z) *
        symmetricTraceProduct w (spectralWeightedMap theta q (fun i => (weights i)⁻¹) w) := by
  let Z := spectralCoordinates theta q z
  let W := spectralCoordinates theta q w
  have h := weighted_cauchy_schwarz
    (![weights 0, weights 1, 2 * weights 2] : Fin 3 → ℝ)
    Z (![W 0, W 1, 2 * W 2] : Fin 3 → ℝ) (by
      intro i
      fin_cases i
      · simpa using hw 0
      · simpa using hw 1
      · simpa using mul_pos (by norm_num : (0 : ℝ) < 2) (hw 2))
  rw [spectralWeightedMap_trace hq, spectralWeightedMap_trace hq]
  rw [← spectralCoordinates_trace_product hq z w]
  dsimp only [Z, W] at h
  simp [Fin.sum_univ_three] at h
  unfold symmetricTraceProduct
  convert! h using 1 <;> field_simp [(hw 0).ne', (hw 1).ne', (hw 2).ne']

theorem spectralWeightedMap_negative_cauchy {theta q : ℝ}
    (hq : q ^ 2 = theta * (1 - theta)) (weights z w : Fin 3 → ℝ)
    (hw : ∀ i, weights i < 0) :
    symmetricTraceProduct z w ^ 2 ≤
      symmetricTraceProduct z (spectralWeightedMap theta q weights z) *
        symmetricTraceProduct w (spectralWeightedMap theta q (fun i => (weights i)⁻¹) w) := by
  have h := spectralWeightedMap_cauchy hq (-weights) z w (fun i => neg_pos.mpr (hw i))
  have he : (fun i => ((-weights) i)⁻¹) = -(fun i => (weights i)⁻¹) := by
    funext i
    simp
  rw [he, spectralWeightedMap_neg, spectralWeightedMap_neg] at h
  unfold symmetricTraceProduct at h ⊢
  simp only [Pi.neg_apply] at h
  convert! h using 1
  ring

end

end ResearchMain.DiagonalSchatten
