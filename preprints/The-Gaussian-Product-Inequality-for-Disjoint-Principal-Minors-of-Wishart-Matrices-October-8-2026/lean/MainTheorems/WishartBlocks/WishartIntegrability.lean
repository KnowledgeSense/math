import MainTheorems.WishartBlocks.BartlettMoments
import MainTheorems.WishartBlocks.BlockMoments
import MainTheorems.WishartBlocks.MatrixGrowth

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators

theorem bartlett_real_growth_integrable {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) {f : (Fin p × Fin p → ℝ) → ℝ} (hf : Measurable f)
    {C β : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ β) :
    Integrable f (bartlettMeasure p α) := by
  let k := ⌈β⌉₊
  apply ((bartlett_input_polynomial_integrable hα k).const_mul C).mono'
    hf.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    calc
      ‖f x‖ ≤ C * (1 + ‖x‖) ^ β := hb x
      _ ≤ C * (1 + ‖x‖) ^ k := by
        rw [← Real.rpow_natCast]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil β)) hC

namespace BlockPartition

noncomputable def determinantBound {p d : ℕ} (P : BlockPartition p d)
    (S : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) : ℝ :=
  Fintype.card (Equiv.Perm (Fin (P.size j))) * (bartlettEntryConstant S) ^ P.size j

theorem determinantBound_nonneg {p d : ℕ} (P : BlockPartition p d)
    (S : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) : 0 ≤ P.determinantBound S j := by
  unfold determinantBound
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (bartlettEntryConstant_nonneg S) _)

theorem block_determinant_growth {p d : ℕ} (P : BlockPartition p d)
    (S : Matrix (Fin p) (Fin p) ℝ) (x : Fin p × Fin p → ℝ) (j : Fin d) :
    ‖(P.block (bartlettValue S x) j).det‖ ≤
      P.determinantBound S j * (1 + ‖x‖) ^ (2 * P.size j) := by
  have h := determinant_entry_bound (P.block (bartlettValue S x) j)
    (fun i k => bartlettValue_entry_bound S x (P.inclusion j i) (P.inclusion j k))
  calc
    ‖(P.block (bartlettValue S x) j).det‖ ≤
        Fintype.card (Equiv.Perm (Fin (P.size j))) *
          (bartlettEntryConstant S * (1 + ‖x‖) ^ 2) ^ P.size j := h
    _ = P.determinantBound S j * (1 + ‖x‖) ^ (2 * P.size j) := by
      unfold determinantBound
      rw [mul_pow, ← pow_mul]
      ring

theorem determinantPower_growth {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (x : Fin p × Fin p → ℝ) (j : Fin d)
    (hν : 0 ≤ ν j) :
    ‖P.determinantPower ν (bartlettValue S x) j‖ ≤
      (P.determinantBound S j) ^ ν j * (1 + ‖x‖) ^ (2 * (P.size j : ℝ) * ν j) := by
  have hd : 0 ≤ (P.block (bartlettValue S x) j).det :=
    ((bartlettValue_positiveSemidefinite S x).submatrix (P.inclusion j)).det_nonneg
  have hB : (P.block (bartlettValue S x) j).det ≤
      P.determinantBound S j * (1 + ‖x‖) ^ (2 * P.size j) := by
    simpa only [Real.norm_of_nonneg hd] using P.block_determinant_growth S x j
  unfold determinantPower
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hd _)]
  calc
    (P.block (bartlettValue S x) j).det ^ ν j ≤
        (P.determinantBound S j * (1 + ‖x‖) ^ (2 * P.size j)) ^ ν j :=
      Real.rpow_le_rpow hd hB hν
    _ = (P.determinantBound S j) ^ ν j *
        (1 + ‖x‖) ^ (2 * (P.size j : ℝ) * ν j) := by
      rw [Real.mul_rpow (P.determinantBound_nonneg S j) (by positivity),
        ← Real.rpow_natCast_mul (by positivity) (2 * P.size j) (ν j)]
      simp only [Nat.cast_mul, Nat.cast_ofNat]

theorem determinantProduct_growth {p d : ℕ} (P : BlockPartition p d) (ν : Fin d → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (x : Fin p × Fin p → ℝ) (hν : ∀ j, 0 ≤ ν j) :
    ‖P.determinantProduct ν (bartlettValue S x)‖ ≤
      (∏ j, (P.determinantBound S j) ^ ν j) *
        (1 + ‖x‖) ^ (∑ j, 2 * (P.size j : ℝ) * ν j) := by
  unfold determinantProduct
  rw [norm_prod]
  calc
    (∏ j, ‖P.determinantPower ν (bartlettValue S x) j‖) ≤
        ∏ j, (P.determinantBound S j) ^ ν j *
          (1 + ‖x‖) ^ (2 * (P.size j : ℝ) * ν j) :=
      Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => norm_nonneg _)
        (fun j _ => P.determinantPower_growth ν S x j (hν j))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity)
        (fun j => 2 * (P.size j : ℝ) * ν j) Finset.univ]

theorem determinantPower_integrable {p d : ℕ} (P : BlockPartition p d)
    {α : ℝ} (hα : (p : ℝ) - 1 < α) (ν : Fin d → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) (hν : 0 ≤ ν j) :
    Integrable (fun W => P.determinantPower ν W j) (bartlettLaw α S) := by
  unfold bartlettLaw
  apply (integrable_map_measure (P.measurable_determinantPower ν j).aestronglyMeasurable
    (measurable_bartlettValue S).aemeasurable).mpr
  apply bartlett_real_growth_integrable hα
    ((P.measurable_determinantPower ν j).comp (measurable_bartlettValue S))
    (Real.rpow_nonneg (P.determinantBound_nonneg S j) (ν j))
  exact fun x => P.determinantPower_growth ν S x j hν

theorem determinantProduct_integrable {p d : ℕ} (P : BlockPartition p d)
    {α : ℝ} (hα : (p : ℝ) - 1 < α) (ν : Fin d → ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (hν : ∀ j, 0 ≤ ν j) :
    Integrable (P.determinantProduct ν) (bartlettLaw α S) := by
  unfold bartlettLaw
  apply (integrable_map_measure (P.measurable_determinantProduct ν).aestronglyMeasurable
    (measurable_bartlettValue S).aemeasurable).mpr
  apply bartlett_real_growth_integrable hα
    ((P.measurable_determinantProduct ν).comp (measurable_bartlettValue S))
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (P.determinantBound_nonneg S j) (ν j))
  exact fun x => P.determinantProduct_growth ν S x hν

end BlockPartition

end ResearchMain.WishartBlocks
