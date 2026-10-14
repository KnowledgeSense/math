import MainTheorems.AHOConstants.SemidefiniteExtension
import MainTheorems.AHOConstants.WordReduction

namespace ResearchMain.AHOConstants

open Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem strict_counterexample_regularized {w : TraceWord} (hw : WordNonnegative w)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) (L : ℝ)
    (hstrict : L * (Matrix.trace (A * B)).re < ‖wordTrace A B w‖) :
    ∃ A' B' : Matrix I I ℂ, A'.PosDef ∧ B'.PosDef ∧
      L * (Matrix.trace (A' * B')).re < ‖wordTrace A' B' w‖ := by
  let T : Matrix I I ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  have hleft := (T.continuous.tendsto (matrixWord A B w)).comp
    (matrixWord_regularized_tendsto hA hB w hw)
  have hright := (T.continuous.tendsto (A * B)).comp
    ((regularized_tendsto A).mul (regularized_tendsto B))
  have hreal := (Complex.continuous_re.tendsto _).comp hright
  have hlarge := (hreal.const_mul L).eventually_lt hleft.norm hstrict
  obtain ⟨j, hj⟩ := hlarge.exists
  exact ⟨regularized A j, regularized B j,
    regularized_posDef hA j, regularized_posDef hB j, hj⟩

omit [Fintype I] in
theorem regularized_realEntries {A : Matrix I I ℂ}
    (hreal : ∀ i j, (A i j).im = 0) (k : ℕ) :
    ∀ i j, (regularized A k i j).im = 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [regularized, Matrix.add_apply, Matrix.smul_apply, hreal]
  · simp [regularized, Matrix.add_apply, Matrix.smul_apply, hij, hreal]

theorem strict_real_counterexample_regularized {w : TraceWord} (hw : WordNonnegative w)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hrealA : ∀ i j, (A i j).im = 0) (hrealB : ∀ i j, (B i j).im = 0) (L : ℝ)
    (hstrict : L * (Matrix.trace (A * B)).re < (wordTrace A B w).re) :
    ∃ A' B' : Matrix I I ℂ, A'.PosDef ∧ B'.PosDef ∧
      (∀ i j, (A' i j).im = 0) ∧ (∀ i j, (B' i j).im = 0) ∧
      L * (Matrix.trace (A' * B')).re < (wordTrace A' B' w).re := by
  let T : Matrix I I ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  have hleft := (T.continuous.tendsto (matrixWord A B w)).comp
    (matrixWord_regularized_tendsto hA hB w hw)
  have hright := (T.continuous.tendsto (A * B)).comp
    ((regularized_tendsto A).mul (regularized_tendsto B))
  have hrealLeft := (Complex.continuous_re.tendsto _).comp hleft
  have hrealRight := (Complex.continuous_re.tendsto _).comp hright
  have hlarge := (hrealRight.const_mul L).eventually_lt hrealLeft hstrict
  obtain ⟨j, hj⟩ := hlarge.exists
  exact ⟨regularized A j, regularized B j, regularized_posDef hA j,
    regularized_posDef hB j, regularized_realEntries hrealA j,
    regularized_realEntries hrealB j, hj⟩

end ResearchMain.AHOConstants
