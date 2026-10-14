import MainTheorems.AHOConstants.MatrixFunctionalCalculus
import MainTheorems.AHOConstants.TraceWords

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem spectralPower_scalar_identity {r : ℝ} (hr : 0 ≤ r) (p : ℝ) :
    spectralPower (r • (1 : Matrix I I ℂ)) p = r ^ p • (1 : Matrix I I ℂ) := by
  have hA : (r • (1 : Matrix I I ℂ)).PosSemidef := Matrix.PosSemidef.one.smul hr
  change (r • (1 : Matrix I I ℂ)) ^ p = _
  rw [CFC.rpow_eq_cfc_real hA.nonneg]
  rw [← Algebra.algebraMap_eq_smul_one r, cfc_algebraMap, Algebra.algebraMap_eq_smul_one]

theorem conjugation_posSemidef {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (U : unitary (Matrix I I ℂ)) :
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U A).PosSemidef := by
  rw [Unitary.conjStarAlgAut_apply]
  simpa only [Matrix.star_eq_conjTranspose] using
    hA.mul_mul_conjTranspose_same (U : Matrix I I ℂ)

theorem spectralPower_conjugation {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (U : unitary (Matrix I I ℂ)) (r : ℝ) :
    spectralPower (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U A) r =
      Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U (spectralPower A r) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  have hφA := conjugation_posSemidef hA U
  change (φ A) ^ r = φ (A ^ r)
  rw [CFC.rpow_eq_cfc_real hφA.nonneg, CFC.rpow_eq_cfc_real hA.nonneg]
  have hφ : Continuous φ :=
    φ.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap.continuous
  exact (StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) φ (fun x : ℝ => x ^ r) A
    ((Matrix.finite_real_spectrum (A := A)).continuousOn _) hφ
    hA.isHermitian.isSelfAdjoint hφA.isHermitian.isSelfAdjoint).symm

theorem matrixWord_cons {A B : Matrix I I ℂ} (cr : Bool × ℝ) (w : TraceWord) :
    matrixWord A B (cr :: w) =
      spectralPower (if cr.1 then A else B) cr.2 * matrixWord A B w := rfl

theorem matrixWord_conjugation {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : unitary (Matrix I I ℂ)) (w : TraceWord) :
    matrixWord (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U A)
      (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U B) w =
      Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U (matrixWord A B w) := by
  let φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U
  induction w with
  | nil => exact (map_one φ).symm
  | cons cr w ih =>
    rw [matrixWord_cons, matrixWord_cons, map_mul, ih]
    cases hc : cr.1
    · simp only [Bool.false_eq_true, ite_false]
      rw [spectralPower_conjugation hB U]
    · simp only [ite_true]
      rw [spectralPower_conjugation hA U]

theorem trace_conjugation (U : unitary (Matrix I I ℂ)) (X : Matrix I I ℂ) :
    Matrix.trace (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U X) = Matrix.trace X := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

theorem wordTrace_conjugation {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : unitary (Matrix I I ℂ)) (w : TraceWord) :
    wordTrace (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U A)
      (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U B) w = wordTrace A B w := by
  unfold wordTrace
  rw [matrixWord_conjugation hA hB U w, trace_conjugation]

end ResearchMain.AHOConstants
