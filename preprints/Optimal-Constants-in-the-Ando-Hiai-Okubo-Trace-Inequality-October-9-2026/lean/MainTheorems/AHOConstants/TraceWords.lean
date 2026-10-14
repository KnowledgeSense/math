import MainTheorems.AHOConstants.SpectralPowers
import Mathlib.LinearAlgebra.Matrix.Trace

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev TraceWord := List (Bool × ℝ)

noncomputable def matrixWord (A B : Matrix I I ℂ) (w : TraceWord) : Matrix I I ℂ :=
  (w.map (fun cr => spectralPower (if cr.1 then A else B) cr.2)).prod

noncomputable def wordTrace (A B : Matrix I I ℂ) (w : TraceWord) : ℂ :=
  Matrix.trace (matrixWord A B w)

noncomputable def exponentMass (c : Bool) (w : TraceWord) : ℝ :=
  (w.map (fun cr => if cr.1 = c then cr.2 else 0)).sum

theorem matrixWord_append (A B : Matrix I I ℂ) (u v : TraceWord) :
    matrixWord A B (u ++ v) = matrixWord A B u * matrixWord A B v := by
  simp [matrixWord, List.prod_append]

theorem wordTrace_rotate (A B : Matrix I I ℂ) (u v : TraceWord) :
    wordTrace A B (u ++ v) = wordTrace A B (v ++ u) := by
  simp only [wordTrace, matrixWord_append]
  exact Matrix.trace_mul_comm _ _

theorem matrixWord_delete_zero (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (u v : TraceWord) (c : Bool) :
    matrixWord A B (u ++ [(c, 0)] ++ v) = matrixWord A B (u ++ v) := by
  have hz : spectralPower (if c then A else B) 0 = 1 := by
    cases c
    · exact spectralPower_zero B hB
    · exact spectralPower_zero A hA
  simp [matrixWord, hz]

theorem matrixWord_merge (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (u v : TraceWord) (c : Bool) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    matrixWord A B (u ++ [(c, x), (c, y)] ++ v) =
      matrixWord A B (u ++ [(c, x + y)] ++ v) := by
  have hm : spectralPower (if c then A else B) (x + y) =
      spectralPower (if c then A else B) x * spectralPower (if c then A else B) y := by
    cases c
    · exact spectralPower_add B hB hx hy
    · exact spectralPower_add A hA hx hy
  simp [matrixWord, hm, Matrix.mul_assoc]

theorem exponentMass_append (c : Bool) (u v : TraceWord) :
    exponentMass c (u ++ v) = exponentMass c u + exponentMass c v := by
  simp [exponentMass, List.sum_append]

theorem exponentMass_delete_zero (d c : Bool) (u v : TraceWord) :
    exponentMass d (u ++ [(c, 0)] ++ v) = exponentMass d (u ++ v) := by
  simp [exponentMass]

theorem exponentMass_merge (d c : Bool) (u v : TraceWord) (x y : ℝ) :
    exponentMass d (u ++ [(c, x), (c, y)] ++ v) =
      exponentMass d (u ++ [(c, x + y)] ++ v) := by
  by_cases h : c = d <;> simp [exponentMass, h, add_assoc]

end ResearchMain.AHOConstants
