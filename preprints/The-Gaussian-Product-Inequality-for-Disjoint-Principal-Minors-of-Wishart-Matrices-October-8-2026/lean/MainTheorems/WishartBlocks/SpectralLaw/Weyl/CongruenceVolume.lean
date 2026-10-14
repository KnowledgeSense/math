import MainTheorems.WishartBlocks.SpectralLaw.Weyl.OrbitGeometry
import MainTheorems.WishartBlocks.SpectralLaw.LowerIndexAlgebra
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace ResearchMain.WishartBlocks.Weyl

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def lowerTraceWeight {n : ℕ} (e : LowerIndex n) : ℝ :=
  if e.val.1 = e.val.2 then 1 else 2

theorem sum_symmetric_lower {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      ∑ i, ∑ j, if j ≤ i then (if i = j then 1 else 2) * f i j else 0 := by
  classical
  have hsplit : (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if j ≤ i then f i j else 0) +
      (∑ i, ∑ j, if i < j then f i j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j ≤ i
    · simp [hji, not_lt_of_ge hji]
    · simp [hji, lt_of_not_ge hji]
  have hupper : (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  rw [hsplit, hupper, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy j i with h | h | h
  · simp [h.le, h, ne_of_gt h]
    ring
  · subst j
    simp
  · simp [not_le_of_gt h, not_lt_of_gt h]

set_option backward.isDefEq.respectTransparency false in
theorem symmetricMatrix_trace_mul {n : ℕ} (x y : LowerIndex n → ℝ) :
    ((symmetricMatrix x) * (symmetricMatrix y)).trace =
      ∑ e : LowerIndex n, lowerTraceWeight e * x e * y e := by
  classical
  have hx (i j : Fin n) : symmetricMatrix x i j = symmetricMatrix x j i := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrArg (fun W : Matrix (Fin n) (Fin n) ℝ => W j i) (symmetricMatrix_isHermitian x)
  have hy (i j : Fin n) : symmetricMatrix y i j = symmetricMatrix y j i := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrArg (fun W : Matrix (Fin n) (Fin n) ℝ => W j i) (symmetricMatrix_isHermitian y)
  calc
    _ = ∑ i, ∑ j, symmetricMatrix x i j * symmetricMatrix y j i := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    _ = ∑ i, ∑ j, if j ≤ i then (if i = j then 1 else 2) *
        (symmetricMatrix x i j * symmetricMatrix y j i) else 0 :=
      sum_symmetric_lower _ (by intro i j; rw [hx i j, hy j i])
    _ = ∑ e : LowerIndex n,
        (if (ofLex e.val).1 = (ofLex e.val).2 then 1 else 2) *
          (symmetricMatrix x (ofLex e.val).1 (ofLex e.val).2 *
            symmetricMatrix y (ofLex e.val).2 (ofLex e.val).1) := by
      simpa only [ofLex_toLex] using (lowerIndex_sum (fun e : Fin n ×ₗ Fin n =>
        (if (ofLex e).1 = (ofLex e).2 then 1 else 2) *
          (symmetricMatrix x (ofLex e).1 (ofLex e).2 *
            symmetricMatrix y (ofLex e).2 (ofLex e).1))).symm
    _ = ∑ e : LowerIndex n, lowerTraceWeight e * x e * y e := by
      apply Finset.sum_congr rfl
      intro e _
      have hxe : symmetricMatrix x (ofLex e.val).1 (ofLex e.val).2 = x e :=
        congrFun (symmetricCoordinates_symmetricMatrix x) e
      have hye : symmetricMatrix y (ofLex e.val).1 (ofLex e.val).2 = y e :=
        congrFun (symmetricCoordinates_symmetricMatrix y) e
      have hentry : symmetricMatrix x (ofLex e.val).1 (ofLex e.val).2 *
          symmetricMatrix y (ofLex e.val).2 (ofLex e.val).1 = x e * y e :=
        congrArg₂ (fun a b : ℝ => a * b) hxe
          ((hy (ofLex e.val).2 (ofLex e.val).1).trans hye)
      change lowerTraceWeight e *
        (symmetricMatrix x (ofLex e.val).1 (ofLex e.val).2 *
          symmetricMatrix y (ofLex e.val).2 (ofLex e.val).1) = _
      calc
        _ = lowerTraceWeight e * (x e * y e) :=
          congrArg (fun a : ℝ => lowerTraceWeight e * a) hentry
        _ = _ := by ring

noncomputable def orthogonalCongruenceLinearMap {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (LowerIndex n → ℝ) →ₗ[ℝ] (LowerIndex n → ℝ) where
  toFun z := symmetricCoordinates (Q.val * symmetricMatrix z * Q.val.transpose)
  map_add' x y := by
    have hsym : symmetricMatrix (x + y) = symmetricMatrix x + symmetricMatrix y := by
      ext i j
      exact (symmetricEntry i j).map_add x y
    rw [hsym, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' c x := by
    have hsym : symmetricMatrix (c • x) = c • symmetricMatrix x := by
      ext i j
      exact (symmetricEntry i j).map_smul c x
    rw [hsym, Matrix.mul_smul, Matrix.smul_mul]
    rfl

@[simp] theorem orthogonalCongruenceLinearMap_one {n : ℕ} (z : LowerIndex n → ℝ) :
    orthogonalCongruenceLinearMap (1 : Matrix.orthogonalGroup (Fin n) ℝ) z = z := by
  change symmetricCoordinates ((1 : Matrix (Fin n) (Fin n) ℝ) *
    symmetricMatrix z * (1 : Matrix (Fin n) (Fin n) ℝ).transpose) = z
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    symmetricCoordinates_symmetricMatrix]

theorem orthogonalCongruenceLinearMap_mul {n : ℕ}
    (Q V : Matrix.orthogonalGroup (Fin n) ℝ) (z : LowerIndex n → ℝ) :
    orthogonalCongruenceLinearMap Q (orthogonalCongruenceLinearMap V z) =
      orthogonalCongruenceLinearMap (Q * V) z := by
  have hherm : (V.val * symmetricMatrix z * V.val.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose V.val (symmetricMatrix_isHermitian z)
  change symmetricCoordinates (Q.val * symmetricMatrix
    (symmetricCoordinates (V.val * symmetricMatrix z * V.val.transpose)) * Q.val.transpose) =
      symmetricCoordinates ((Q * V).val * symmetricMatrix z * (Q * V).val.transpose)
  rw [symmetricMatrix_symmetricCoordinates hherm]
  simp only [Submonoid.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem orthogonalCongruence_trace_mul {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (x y : LowerIndex n → ℝ) :
    ((symmetricMatrix (orthogonalCongruenceLinearMap Q x)) *
      (symmetricMatrix (orthogonalCongruenceLinearMap Q y))).trace =
        ((symmetricMatrix x) * (symmetricMatrix y)).trace := by
  have hherm (z : LowerIndex n → ℝ) :
      (Q.val * symmetricMatrix z * Q.val.transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose Q.val (symmetricMatrix_isHermitian z)
  change ((symmetricMatrix (symmetricCoordinates (Q.val * symmetricMatrix x * Q.val.transpose))) *
    (symmetricMatrix (symmetricCoordinates (Q.val * symmetricMatrix y * Q.val.transpose)))).trace = _
  rw [symmetricMatrix_symmetricCoordinates (hherm x),
    symmetricMatrix_symmetricCoordinates (hherm y)]
  calc
    _ = (Q.val * (symmetricMatrix x * symmetricMatrix y) * Q.val.transpose).trace := by
      congr 1
      calc
        _ = Q.val * symmetricMatrix x * (Q.val.transpose * Q.val) *
            symmetricMatrix y * Q.val.transpose := by simp only [Matrix.mul_assoc]
        _ = _ := by simp only [(Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property,
          Matrix.mul_one, Matrix.mul_assoc]
    _ = ((Q.val.transpose * Q.val) * (symmetricMatrix x * symmetricMatrix y)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = _ := by rw [(Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property, Matrix.one_mul]

theorem orthogonalCongruence_gram {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    let C := LinearMap.toMatrix' (orthogonalCongruenceLinearMap Q)
    C.transpose * Matrix.diagonal lowerTraceWeight * C =
      Matrix.diagonal lowerTraceWeight := by
  classical
  dsimp only
  ext e f
  have h := orthogonalCongruence_trace_mul Q (Pi.single e 1) (Pi.single f 1)
  rw [symmetricMatrix_trace_mul, symmetricMatrix_trace_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    LinearMap.toMatrix'_apply]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · by_cases hef : e = f
    · subst f
      simp [Pi.single_apply]
    · simp [Pi.single_apply, hef, Ne.symm hef]

theorem orthogonalCongruence_abs_det {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    |(LinearMap.toMatrix' (orthogonalCongruenceLinearMap Q)).det| = 1 := by
  have hgram := congrArg Matrix.det (orthogonalCongruence_gram Q)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hgram
  have hG : (Matrix.diagonal (lowerTraceWeight (n := n))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro e _
    simp only [lowerTraceWeight]
    split_ifs <;> norm_num
  have hsq : (LinearMap.toMatrix' (orthogonalCongruenceLinearMap Q)).det *
      (LinearMap.toMatrix' (orthogonalCongruenceLinearMap Q)).det = 1 := by
    apply mul_right_cancel₀ hG
    nlinarith [hgram]
  rcases mul_self_eq_one_iff.mp hsq with h | h <;> rw [h] <;> norm_num

theorem orthogonalCongruence_map_volume {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (volume : Measure (LowerIndex n → ℝ)).map (orthogonalCongruenceLinearMap Q) = volume := by
  have hdet : |LinearMap.det (orthogonalCongruenceLinearMap Q)| = 1 := by
    simpa only [LinearMap.det_toMatrix'] using orthogonalCongruence_abs_det Q
  have hne : LinearMap.det (orthogonalCongruenceLinearMap Q) ≠ 0 := by
    intro h
    simp only [h, abs_zero, zero_ne_one] at hdet
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne,
    abs_inv, hdet, inv_one, ENNReal.ofReal_one, one_smul]

theorem orthogonalCongruence_measurePreserving {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (orthogonalCongruenceLinearMap Q)
      (volume : Measure (LowerIndex n → ℝ)) volume :=
  ⟨(orthogonalCongruenceLinearMap Q).continuous_of_finiteDimensional.measurable,
    orthogonalCongruence_map_volume Q⟩

theorem orthogonalCongruence_lintegral {n : ℕ}
    (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    {G : (LowerIndex n → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ W, G (orthogonalCongruenceLinearMap Q W)) = ∫⁻ W, G W := by
  rw [← lintegral_map hG (orthogonalCongruenceLinearMap Q).continuous_of_finiteDimensional.measurable,
    orthogonalCongruence_map_volume]

end ResearchMain.WishartBlocks.Weyl
