import MainTheorems.DiagonalSchatten.FiniteBlocks
import MainTheorems.DiagonalSchatten.GramCompression
import MainTheorems.DiagonalSchatten.OperatorCompression

namespace ResearchMain.DiagonalSchatten

noncomputable section

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

theorem diagonal_schatten_compression_lower {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (compression p z) ≤ schattenNorm p (diagonalBlockMatrix z) :=
  finite_diagonal_block_lower hp hp2 z

theorem diagonal_schatten_compression_upper {p : ℝ} (hp : 2 ≤ p)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (diagonalBlockMatrix z) ≤ schattenNorm p (compression p z) := by
  rcases le_total p 4 with hp4 | hp4
  · exact finite_diagonal_block_upper_to_four hp hp4 z
  · exact diagonal_compression_above_four hp4 z

open scoped Matrix.Norms.L2Operator in
theorem diagonal_schatten_compression_infinity (z : Fin 2 → J → D → ℂ) :
    ‖diagonalBlockMatrix z‖ ≤ ‖operatorCompression z‖ :=
  diagonal_operator_compression z

end

end ResearchMain.DiagonalSchatten
