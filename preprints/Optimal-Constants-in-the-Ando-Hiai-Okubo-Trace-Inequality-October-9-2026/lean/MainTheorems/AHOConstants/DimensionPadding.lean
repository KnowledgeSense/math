import MainTheorems.AHOConstants.ZeroPadding
import MainTheorems.AHOConstants.MatrixReindexPowers
import MainTheorems.AHOConstants.InfeasibleCounterexample
import MainTheorems.AHOConstants.CounterexampleStability
import MainTheorems.AHOConstants.OptimalConstants
import Mathlib.Logic.Equiv.Fin.Basic

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

theorem ExponentData.padded_psd_real_counterexample (d : ExponentData) (hd : ¬d.feasible)
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin (3 + m)) (Fin (3 + m)) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧
        (∀ i j, (A i j).im = 0) ∧ (∀ i j, (B i j).im = 0) ∧
          L * (Matrix.trace (A * B)).re < (wordTrace A B d.word).re := by
  obtain ⟨A, B, hA, hB, hrealA, hrealB, _, hlarge⟩ :=
    d.infeasible_psd_real_counterexample hd L hL
  let P := zeroPadding (J := Fin m) A
  let Q := zeroPadding (J := Fin m) B
  have hP : P.PosSemidef := zeroPadding_posSemidef hA
  have hQ : Q.PosSemidef := zeroPadding_posSemidef hB
  let e : Fin 3 ⊕ Fin m ≃ Fin (3 + m) := finSumFinEquiv
  let φ := matrixReindexStarAlgEquiv e
  have hword : wordTrace (φ P) (φ Q) d.word = wordTrace A B d.word := by
    rw [matrixReindex_wordTrace e hP hQ]
    unfold ExponentData.word
    apply zeroPadding_pairTrace hA hB
    · intro he
      have hl := congrArg List.length he
      simp only [List.length_ofFn, List.length_nil] at hl
      omega
    · intro pq hpq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hpq
      exact ⟨d.p_positive i, d.q_positive i⟩
  have hdenom : Matrix.trace (φ P * φ Q) = Matrix.trace (A * B) := by
    rw [← map_mul φ, matrixReindex_trace]
    change Matrix.trace (zeroPadding (J := Fin m) A * zeroPadding B) = _
    rw [← zeroPadding_mul, zeroPadding_trace]
  refine ⟨φ P, φ Q, matrixReindex_posSemidef e hP, matrixReindex_posSemidef e hQ,
    matrixReindex_realEntries e (zeroPadding_realEntries hrealA),
    matrixReindex_realEntries e (zeroPadding_realEntries hrealB), ?_⟩
  rw [hword, hdenom]
  exact hlarge

theorem ExponentData.padded_psd_counterexample (d : ExponentData) (hd : ¬d.feasible)
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin (3 + m)) (Fin (3 + m)) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧
        L * (Matrix.trace (A * B)).re < ‖wordTrace A B d.word‖ := by
  obtain ⟨A, B, hA, hB, _, _, hlarge⟩ := d.padded_psd_real_counterexample hd m L hL
  exact ⟨A, B, hA, hB, hlarge.trans_le (Complex.re_le_norm _)⟩

theorem infeasibleWord_real_pd_counterexample {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    (hinfeasible : ¬FeasibleWord w) (n : ℕ) (hn : 3 ≤ n) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧ B.PosDef ∧
        (∀ i j, (A i j).im = 0) ∧ (∀ i j, (B i j).im = 0) ∧
          0 < (wordTrace A B w).re ∧
            L < (wordTrace A B w).re / (Matrix.trace (A * B)).re := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨d, hred⟩ := normalized_reduced_data hw hAmass hBmass
  have hd : ¬d.feasible := fun hf => hinfeasible ⟨d, hred, hf⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨A, B, hA, hB, hrealA, hrealB, hlarge⟩ :=
    d.padded_psd_real_counterexample hd m L hL
  have hlarge' : L * (Matrix.trace (A * B)).re < (wordTrace A B w).re := by
    rw [hred.trace A B hA hB]
    exact hlarge
  obtain ⟨A', B', hA', hB', hrealA', hrealB', hstrict⟩ :=
    strict_real_counterexample_regularized hw hA hB hrealA hrealB L hlarge'
  have hdenom := trace_product_positive hA' hB'
  exact ⟨A', B', hA', hB', hrealA', hrealB',
    lt_of_le_of_lt (mul_nonneg hL hdenom.le) hstrict,
    (lt_div_iff₀ hdenom).mpr hstrict⟩

theorem infeasibleWord_pd_counterexample {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    (hinfeasible : ¬FeasibleWord w) (n : ℕ) (hn : 3 ≤ n) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧ B.PosDef ∧ L * (Matrix.trace (A * B)).re < ‖wordTrace A B w‖ := by
  obtain ⟨d, hred⟩ := normalized_reduced_data hw hAmass hBmass
  have hd : ¬d.feasible := fun hf => hinfeasible ⟨d, hred, hf⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨A, B, hA, hB, hlarge⟩ := d.padded_psd_counterexample hd m L hL
  have hlarge' : L * (Matrix.trace (A * B)).re < ‖wordTrace A B w‖ := by
    rw [hred.trace A B hA hB]
    exact hlarge
  exact strict_counterexample_regularized hw hA hB L hlarge'

theorem optimalConstant_infinite_of_infeasibleWord {w : TraceWord} (hw : WordNonnegative w)
    (hAmass : exponentMass true w = 1) (hBmass : exponentMass false w = 1)
    (hinfeasible : ¬FeasibleWord w) (n : ℕ) (hn : 3 ≤ n) :
    optimalConstant n w = ∞ := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_contra hfinite
  let L : ℝ := (optimalConstant n w).toReal + 1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨A, B, hA, hB, hlarge⟩ := infeasibleWord_pd_counterexample hw hAmass hBmass
    hinfeasible n hn L hL
  have hratio : L < traceRatio A B w := by
    unfold traceRatio
    exact (lt_div_iff₀ (trace_product_positive hA hB)).mpr hlarge
  have hupper : ENNReal.ofReal (traceRatio A B w) ≤ optimalConstant n w := by
    unfold optimalConstant
    exact le_iSup_of_le A (le_iSup_of_le B
      (le_iSup_of_le hA (le_iSup_of_le hB le_rfl)))
  have htoo : optimalConstant n w < ENNReal.ofReal (traceRatio A B w) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr
    dsimp [L] at hratio
    linarith
  exact not_lt_of_ge hupper htoo

end ResearchMain.AHOConstants
