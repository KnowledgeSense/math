import MainTheorems.DiagonalSchatten.PositiveDeterminantDomain
import MainTheorems.DiagonalSchatten.SymmetricHessianQuadratic

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem positiveDeterminantArrays_rootGram {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays) :
    0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2 := by
  rw [twoByTwo_gramDet_eq_det_sq]
  exact sq_pos_of_pos ((entryRoot_determinant_positive_iff hp B hB.1).mpr hB.2)

theorem compressionHessian_principal_hermitian {p : ℝ} (hp : 0 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays) :
    (radialPrincipalMinor (compressionHessianMatrix p B)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial, radialPrincipalMinor]
  exact compressionHessianMatrix_symmetric hp B hB.1
    (positiveDeterminantArrays_rootGram hp B hB) _ _

theorem compressionHessian_principal_continuousOn {p : ℝ} (hp : 0 < p) :
    ContinuousOn (fun B => radialPrincipalMinor (compressionHessianMatrix p B))
      positiveDeterminantArrays := by
  intro B hB
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  have h2 := contDiffAt_compressionFunctional_fullRank (n := 2) hp B hB.1
    (positiveDeterminantArrays_rootGram hp B hB)
  have hc : ContinuousAt (compressionHessian p) B :=
    (h2.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  exact ((hc.clm_apply continuousAt_const).clm_apply continuousAt_const).continuousWithinAt

theorem symmetric_power_positiveDeterminant {p h : ℝ} (hp : 0 < p)
    (hh : 0 < h) (hh1 : h < 1) : rationalSVDPowers p h 1 1 ∈ positiveDeterminantArrays := by
  have hM := symmetric_core_positive hh hh1
  refine ⟨rationalSVDPowers_positive hM, ?_⟩
  apply (entryRoot_determinant_positive_iff hp _ (rationalSVDPowers_positive hM)).mp
  change 0 < (realEntryRoot p (realEntryPowers p (rationalSVDCore 1 1 h))).det
  rw [realEntryRoot_realEntryPowers hp.ne' _ (fun i j => (hM i j).le)]
  simp [Matrix.det_fin_two, rationalSVDCore]
  nlinarith

theorem symmetric_principal_posSemidef {p h : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hh : 0 < h) (hh1 : h < 1) :
    (radialPrincipalMinor (compressionHessianMatrix p (rationalSVDPowers p h 1 1))).PosSemidef := by
  have hB := symmetric_power_positiveDeterminant (by linarith : 0 < p) hh hh1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (compressionHessian_principal_hermitian (by linarith) _ hB)
  intro v
  rw [radialPrincipalMinor_quadratic, compressionHessianMatrix_quadratic]
  exact symmetric_compressionHessian_nonneg hp hp2 hh hh1 _

theorem symmetric_neg_principal_posSemidef {p h : ℝ} (hp : 2 < p)
    (hh : 0 < h) (hh1 : h < 1) :
    (-(radialPrincipalMinor (compressionHessianMatrix p (rationalSVDPowers p h 1 1)))).PosSemidef := by
  have hB := symmetric_power_positiveDeterminant (by linarith : 0 < p) hh hh1
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (compressionHessian_principal_hermitian (by linarith) _ hB).neg
  intro v
  simp only [Matrix.neg_mulVec, dotProduct_neg]
  rw [radialPrincipalMinor_quadratic, compressionHessianMatrix_quadratic]
  exact neg_nonneg.mpr (symmetric_compressionHessian_nonpos hp hh hh1 _)

theorem compressionHessian_principal_positive {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays) :
    (radialPrincipalMinor (compressionHessianMatrix p B)).PosDef := by
  have hp0 : 0 < p := by linarith
  let B0 := rationalSVDPowers p (1 / 2) 1 1
  have hB0 : B0 ∈ positiveDeterminantArrays := symmetric_power_positiveDeterminant hp0
    (by norm_num) (by norm_num)
  have hdet (Y) (hY : Y ∈ positiveDeterminantArrays) :
      (radialPrincipalMinor (compressionHessianMatrix p Y)).det ≠ 0 := by
    apply compressionHessian_principal_det_ne_zero hp (by linarith) Y hY.1
    exact ((entryRoot_determinant_positive_iff hp0 Y hY.1).mpr hY.2).ne'
  have hbase : (radialPrincipalMinor (compressionHessianMatrix p B0)).PosDef :=
    (symmetric_principal_posSemidef hp hp2 (by norm_num) (by norm_num)).posDef_iff_det_ne_zero.mpr
      (hdet B0 hB0)
  exact positiveDefinite_continuation positiveDeterminantArrays_preconnected
    (fun Y => radialPrincipalMinor (compressionHessianMatrix p Y))
    (compressionHessian_principal_continuousOn hp0)
    (fun Y hY => compressionHessian_principal_hermitian hp0 Y hY) hdet hB0 hbase B hB

theorem compressionHessian_neg_principal_positive {p : ℝ} (hp : 2 < p)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : B ∈ positiveDeterminantArrays) :
    (-(radialPrincipalMinor (compressionHessianMatrix p B))).PosDef := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  let B0 := rationalSVDPowers p (1 / 2) 1 1
  have hB0 : B0 ∈ positiveDeterminantArrays := symmetric_power_positiveDeterminant hp0
    (by norm_num) (by norm_num)
  have hdet (Y) (hY : Y ∈ positiveDeterminantArrays) :
      (-(radialPrincipalMinor (compressionHessianMatrix p Y))).det ≠ 0 := by
    rw [Matrix.det_neg]
    apply mul_ne_zero (by norm_num)
    apply compressionHessian_principal_det_ne_zero hp1 (by linarith) Y hY.1
    exact ((entryRoot_determinant_positive_iff hp0 Y hY.1).mpr hY.2).ne'
  have hbase : (-(radialPrincipalMinor (compressionHessianMatrix p B0))).PosDef :=
    (symmetric_neg_principal_posSemidef hp (by norm_num) (by norm_num)).posDef_iff_det_ne_zero.mpr
      (hdet B0 hB0)
  exact positiveDefinite_continuation positiveDeterminantArrays_preconnected
    (fun Y => -(radialPrincipalMinor (compressionHessianMatrix p Y)))
    (compressionHessian_principal_continuousOn hp0).neg
    (fun Y hY => (compressionHessian_principal_hermitian hp0 Y hY).neg) hdet hB0 hbase B hB

end

end ResearchMain.DiagonalSchatten
