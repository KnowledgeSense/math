import MainTheorems.DiagonalSchatten.CompressionFunctional
import Mathlib.Analysis.Matrix.Normed

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {I J D : Type*} [Fintype I] [Fintype J] [Fintype D]
  [DecidableEq I] [DecidableEq J] [DecidableEq D]

omit [Fintype D] [DecidableEq D] [DecidableEq I] in
theorem continuousOn_schattenPower_exponent (A : Matrix I J ℂ) :
    ContinuousOn (fun p : ℝ => schattenPower p A) (Set.Ioi 0) := by
  unfold schattenPower
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.rpow continuousOn_id (fun p hp => Or.inr hp)

omit [Fintype D] [DecidableEq D] [DecidableEq I] in
theorem continuousOn_schattenNorm_exponent (A : Matrix I J ℂ) :
    ContinuousOn (fun p : ℝ => schattenNorm p A) (Set.Ioi 0) := by
  unfold schattenNorm
  apply (continuousOn_schattenPower_exponent A).rpow
    (continuousOn_const.div continuousOn_id (fun p hp => (show 0 < p from hp).ne'))
  intro p hp
  exact Or.inr (one_div_pos.mpr hp)

omit [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D] in
theorem continuousOn_twoRowPower_exponent (F : ℝ → Matrix (Fin 2) J ℂ)
    (hF : ContinuousOn F (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ => schattenPower p (F p)) (Set.Ioi 0) := by
  have hplus : Continuous (fun W : Matrix (Fin 2) J ℂ =>
      twoEigenvaluePlus (rowMass W 0) (rowMass W 1) (rowCross W)) := by
    unfold twoEigenvaluePlus twoEigenvalueGap rowMass rowCross
    fun_prop
  have hminus : Continuous (fun W : Matrix (Fin 2) J ℂ =>
      twoEigenvalueMinus (rowMass W 0) (rowMass W 1) (rowCross W)) := by
    unfold twoEigenvalueMinus twoEigenvalueGap rowMass rowCross
    fun_prop
  have hsum : ContinuousOn (fun p : ℝ =>
      twoEigenvaluePlus (rowMass (F p) 0) (rowMass (F p) 1) (rowCross (F p)) ^ (p / 2) +
      twoEigenvalueMinus (rowMass (F p) 0) (rowMass (F p) 1) (rowCross (F p)) ^ (p / 2))
      (Set.Ioi 0) :=
    ((hplus.comp_continuousOn hF).rpow (continuousOn_id.div_const 2)
      (fun p hp => Or.inr (div_pos (show 0 < p from hp) (by norm_num)))).add
    ((hminus.comp_continuousOn hF).rpow (continuousOn_id.div_const 2)
      (fun p hp => Or.inr (div_pos (show 0 < p from hp) (by norm_num))))
  exact hsum.congr fun p hp => schattenPower_twoRow hp (F p)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem continuousOn_compression_exponent (z : Fin 2 → J → D → ℂ) :
    ContinuousOn (fun p : ℝ => compression p z) (Set.Ioi 0) := by
  change ContinuousOn (fun p : ℝ => fun i j => (schattenNorm p (diagonalBlock z i j) : ℂ))
    (Set.Ioi 0)
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_schattenNorm_exponent (diagonalBlock z i j))

omit [Fintype I] [DecidableEq I] in
theorem continuousOn_compressedNorm_exponent (z : Fin 2 → J → D → ℂ) :
    ContinuousOn (fun p : ℝ => schattenNorm p (compression p z)) (Set.Ioi 0) := by
  unfold schattenNorm
  apply (continuousOn_twoRowPower_exponent _ (continuousOn_compression_exponent z)).rpow
    (continuousOn_const.div continuousOn_id (fun p hp => (show 0 < p from hp).ne'))
  intro p hp
  exact Or.inr (one_div_pos.mpr hp)

end

end ResearchMain.DiagonalSchatten
