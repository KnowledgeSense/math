import MainTheorems.AHOConstants.FeasibleBound
import MainTheorems.AHOConstants.ReducedData
import MainTheorems.AHOConstants.OptimalConstants
import MainTheorems.AHOConstants.SemidefiniteExtension

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

theorem feasibleWord_trace_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {w : TraceWord} (hw : FeasibleWord w) {A B : Matrix I I ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨d, hred, hfeas⟩ := hw
  rw [hred.trace A B hA.posSemidef hB.posSemidef]
  exact feasible_trace_bound d.q_total hfeas hA hB

theorem optimalConstant_eq_one_of_feasibleWord (n : ℕ) (hn : 0 < n)
    {w : TraceWord} (hw : FeasibleWord w) : optimalConstant n w = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm _ (optimalConstant_lower_bound n hn w)
  unfold optimalConstant
  refine iSup_le (fun A => iSup_le (fun B => iSup_le (fun hA => iSup_le (fun hB => ?_))))
  apply ENNReal.ofReal_le_one.mpr
  exact (div_le_one (trace_product_positive hA hB)).mpr (feasibleWord_trace_bound hw hA hB)

theorem feasibleWord_trace_bound_semidefinite {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] {w : TraceWord} (hn : WordNonnegative w)
    (hw : FeasibleWord w) {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re :=
  extend_trace_bound_to_semidefinite hn (fun hP hQ => feasibleWord_trace_bound hw hP hQ) hA hB

end ResearchMain.AHOConstants
