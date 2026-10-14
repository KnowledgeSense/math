import MainTheorems.AHOConstants.TraceWords
import MainTheorems.AHOConstants.TracePositivity
import Mathlib.Basic.ENNReal.Real

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder ENNReal

noncomputable def traceRatio {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (w : TraceWord) : ℝ :=
  ‖wordTrace A B w‖ / (Matrix.trace (A * B)).re

noncomputable def optimalConstant (n : ℕ) (w : TraceWord) : ℝ≥0∞ :=
  ⨆ (A : Matrix (Fin n) (Fin n) ℂ), ⨆ (B : Matrix (Fin n) (Fin n) ℂ),
    ⨆ (_ : A.PosDef), ⨆ (_ : B.PosDef),
    ENNReal.ofReal (traceRatio A B w)

theorem identity_word (n : ℕ) (w : TraceWord) :
    matrixWord (1 : Matrix (Fin n) (Fin n) ℂ) 1 w = 1 := by
  unfold matrixWord
  have hf : (fun cr : Bool × ℝ =>
      spectralPower (if cr.1 then (1 : Matrix (Fin n) (Fin n) ℂ) else 1) cr.2) =
      fun _ => 1 := by
    funext cr
    simp [spectralPower_identity]
  rw [hf]
  simp

theorem identity_traceRatio (n : ℕ) (hn : 0 < n) (w : TraceWord) :
    traceRatio (1 : Matrix (Fin n) (Fin n) ℂ) 1 w = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp only [traceRatio, wordTrace, identity_word, Matrix.one_mul, Matrix.trace_one,
    Fintype.card_fin, Complex.natCast_re, Complex.norm_natCast]
  exact div_self hn'

theorem optimalConstant_lower_bound (n : ℕ) (hn : 0 < n) (w : TraceWord) :
    1 ≤ optimalConstant n w := by
  unfold optimalConstant
  apply le_iSup_of_le (1 : Matrix (Fin n) (Fin n) ℂ)
  apply le_iSup_of_le (1 : Matrix (Fin n) (Fin n) ℂ)
  apply le_iSup_of_le Matrix.PosDef.one
  apply le_iSup_of_le Matrix.PosDef.one
  rw [identity_traceRatio n hn w, ENNReal.ofReal_one]

end ResearchMain.AHOConstants
