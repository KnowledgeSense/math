import MainTheorems.AHOConstants.OptimalConstants
import MainTheorems.AHOConstants.PositiveTrace
import MainTheorems.AHOConstants.WordReduction
import MainTheorems.AHOConstants.SemidefiniteExtension

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

theorem exponentMass_cons (c : Bool) (cr : Bool × ℝ) (w : TraceWord) :
    exponentMass c (cr :: w) = (if cr.1 = c then cr.2 else 0) + exponentMass c w := rfl

theorem exponentMass_nonnegative (c : Bool) (w : TraceWord) (hw : WordNonnegative w) :
    0 ≤ exponentMass c w := by
  revert hw
  induction w with
  | nil => intro _; exact le_refl 0
  | cons cr w ih =>
    intro hw
    have ht := ih (fun d hd => hw d (by simp [hd]))
    change 0 ≤ (if cr.1 = c then cr.2 else 0) + exponentMass c w
    split_ifs
    · exact add_nonneg (hw cr (by simp)) ht
    · simpa only [zero_add] using ht

theorem matrices_commute_one_dimension (X Y : Matrix (Fin 1) (Fin 1) ℂ) : X * Y = Y * X := by
  ext i j
  have hi : i = 0 := by apply Fin.ext; have := i.isLt; simp only [Fin.val_zero]; omega
  have hj : j = 0 := by apply Fin.ext; have := j.isLt; simp only [Fin.val_zero]; omega
  subst i
  subst j
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  exact mul_comm _ _

theorem matrixWord_one_dimension {A B : Matrix (Fin 1) (Fin 1) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (w : TraceWord) (hw : WordNonnegative w) :
    matrixWord A B w =
      spectralPower A (exponentMass true w) * spectralPower B (exponentMass false w) := by
  revert hw
  induction w with
  | nil => intro _; simp only [matrixWord, exponentMass, List.map_nil, List.prod_nil,
      List.sum_nil, spectralPower_zero A hA, spectralPower_zero B hB, Matrix.one_mul]
  | cons cr w ih =>
    intro hw
    have ht : WordNonnegative w := fun d hd => hw d (by simp [hd])
    have ha := exponentMass_nonnegative true w ht
    have hb := exponentMass_nonnegative false w ht
    have hr := hw cr (by simp)
    cases hc : cr.1
    · have he : matrixWord A B (cr :: w) = spectralPower
          (if cr.1 then A else B) cr.2 * matrixWord A B w := rfl
      rw [he, hc]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih ht]
      rw [exponentMass_cons, exponentMass_cons]
      simp only [hc,
        Bool.false_eq_true, ite_false, ite_true, zero_add]
      calc
        _ = (spectralPower B cr.2 * spectralPower A (exponentMass true w)) *
          spectralPower B (exponentMass false w) := by rw [Matrix.mul_assoc]
        _ = spectralPower A (exponentMass true w) *
          (spectralPower B cr.2 * spectralPower B (exponentMass false w)) := by
          rw [matrices_commute_one_dimension (spectralPower B cr.2)
            (spectralPower A (exponentMass true w)), Matrix.mul_assoc]
        _ = _ := by rw [← spectralPower_add B hB hr hb]
    · have he : matrixWord A B (cr :: w) = spectralPower
          (if cr.1 then A else B) cr.2 * matrixWord A B w := rfl
      rw [he, hc]
      simp only [ite_true]
      rw [ih ht]
      rw [exponentMass_cons, exponentMass_cons]
      simp only [hc, ite_true,
        Bool.true_eq_false, ite_false, zero_add]
      rw [← Matrix.mul_assoc, ← spectralPower_add A hA hr ha]

theorem wordTrace_one_dimension {w : TraceWord} (hw : WordNonnegative w)
    (hp : exponentMass true w = 1) (hq : exponentMass false w = 1)
    {A B : Matrix (Fin 1) (Fin 1) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    wordTrace A B w = Matrix.trace (A * B) := by
  unfold wordTrace
  rw [matrixWord_one_dimension hA hB w hw, hp, hq,
    spectralPower_one A hA, spectralPower_one B hB]

theorem optimalConstant_one_dimension {w : TraceWord} (hw : WordNonnegative w)
    (hp : exponentMass true w = 1) (hq : exponentMass false w = 1) :
    optimalConstant 1 w = 1 := by
  have : Nonempty (Fin 1) := ⟨0⟩
  apply le_antisymm _ (optimalConstant_lower_bound 1 (by decide) w)
  unfold optimalConstant
  refine iSup_le (fun A => iSup_le (fun B => iSup_le (fun hA => iSup_le (fun hB => ?_))))
  apply ENNReal.ofReal_le_one.mpr
  unfold traceRatio
  rw [wordTrace_one_dimension hw hp hq hA.posSemidef hB.posSemidef,
    trace_product_norm_positive hA hB,
    div_self (trace_product_positive hA hB).ne']

theorem one_dimension_trace_bound_semidefinite {w : TraceWord} (hw : WordNonnegative w)
    (hp : exponentMass true w = 1) (hq : exponentMass false w = 1)
    {A B : Matrix (Fin 1) (Fin 1) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re := by
  have : Nonempty (Fin 1) := ⟨0⟩
  apply extend_trace_bound_to_semidefinite hw _ hA hB
  intro P Q hP hQ
  rw [wordTrace_one_dimension hw hp hq hP.posSemidef hQ.posSemidef]
  exact (trace_product_norm_positive hP hQ).le

end ResearchMain.AHOConstants
