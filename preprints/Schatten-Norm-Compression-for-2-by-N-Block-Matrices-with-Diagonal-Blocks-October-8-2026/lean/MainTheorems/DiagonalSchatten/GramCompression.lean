import MainTheorems.DiagonalSchatten.DiagonalLp
import MainTheorems.DiagonalSchatten.GramSchattenIdentity
import MainTheorems.DiagonalSchatten.TwoColumnBlocks
import MainTheorems.DiagonalSchatten.TwoColumnMonotone

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D] [DecidableEq J] [DecidableEq D]

def gramDiagonal (z : Fin 2 → J → D → ℂ) : Fin 2 → Fin 2 → D → ℂ :=
  fun i k d => ∑ j, z i j d * star (z k j d)

def gramNormMatrix (q : ℝ) (z : Fin 2 → J → D → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => schattenNorm q (Matrix.diagonal (gramDiagonal z i k))

def blockNormGram (p : ℝ) (z : Fin 2 → J → D → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => ∑ j, schattenNorm p (Matrix.diagonal (z i j)) *
    schattenNorm p (Matrix.diagonal (z k j))

omit [Fintype D] [DecidableEq J] [DecidableEq D] in
theorem gramDiagonal_component (z : Fin 2 → J → D → ℂ) (d : D) :
    Matrix.of (fun i k => gramDiagonal z i k d) =
      Matrix.of (fun i j => z i j d) *
        (Matrix.of (fun i j => z i j d)).conjTranspose := by
  ext i k
  rfl

theorem gramDiagonal_schattenPower {q : ℝ} (hq : 0 < q)
    (z : Fin 2 → J → D → ℂ) :
    schattenPower q (diagonalBlockMatrix (gramDiagonal z)) =
      schattenPower (2 * q) (diagonalBlockMatrix z) := by
  rw [diagonalBlockMatrix_schattenPower, diagonalBlockMatrix_schattenPower]
  apply Finset.sum_congr rfl
  intro d _
  change schattenPower q (Matrix.of (fun i k => gramDiagonal z i k d)) =
    schattenPower (2 * q) (Matrix.of (fun i j => z i j d))
  rw [gramDiagonal_component]
  exact schattenPower_twoRow_gram hq _

omit [DecidableEq J] in
theorem gramNormMatrix_complexify (q : ℝ) (z : Fin 2 → J → D → ℂ) :
    complexifyRows (gramNormMatrix q z) = compression q (gramDiagonal z) := by
  ext i k
  rfl

omit [DecidableEq J] in
theorem blockNormGram_complexify (p : ℝ) (z : Fin 2 → J → D → ℂ) :
    complexifyRows (blockNormGram p z) = compression p z * (compression p z).conjTranspose := by
  ext i k
  simp [complexifyRows, blockNormGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    compression, diagonalBlock, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

omit [DecidableEq J] in
theorem gramNormMatrix_nonnegative (q : ℝ) (z : Fin 2 → J → D → ℂ) (i k : Fin 2) :
    0 ≤ gramNormMatrix q z i k := schattenNorm_nonneg _ _

theorem gramNormMatrix_le_blockNormGram {q : ℝ} (hq : 1 ≤ q)
    (z : Fin 2 → J → D → ℂ) (i k : Fin 2) :
    gramNormMatrix q z i k ≤ blockNormGram (2 * q) z i k := by
  have hsum : gramDiagonal z i k = ∑ j, (fun d => z i j d * star (z k j d)) := by
    ext d
    simp [gramDiagonal]
  change schattenNorm q (Matrix.diagonal (gramDiagonal z i k)) ≤ _
  rw [hsum]
  exact (diagonal_norm_sum hq Finset.univ (fun j d => z i j d * star (z k j d))).trans
    (Finset.sum_le_sum fun j _ => diagonal_norm_product (by linarith : 0 < q) (z i j) (z k j))

theorem diagonal_compression_above_four_power {p : ℝ} (hp : 4 ≤ p)
    (z : Fin 2 → J → D → ℂ) :
    schattenPower p (diagonalBlockMatrix z) ≤ schattenPower p (compression p z) := by
  let q := p / 2
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hpq : p = 2 * q := by dsimp [q]; ring
  rw [hpq]
  calc
    _ = schattenPower q (diagonalBlockMatrix (gramDiagonal z)) :=
      (gramDiagonal_schattenPower hq0 z).symm
    _ ≤ schattenPower q (compression q (gramDiagonal z)) :=
      two_column_diagonal_block_power_upper hq _
    _ = schattenPower q (complexifyRows (gramNormMatrix q z)) := by
      rw [gramNormMatrix_complexify]
    _ ≤ schattenPower q (complexifyRows (blockNormGram (2 * q) z)) :=
      nonnegative_two_column_power_monotone hq _ _ (gramNormMatrix_nonnegative q z)
        (gramNormMatrix_le_blockNormGram (by linarith) z)
    _ = schattenPower (2 * q) (compression (2 * q) z) := by
      rw [blockNormGram_complexify, schattenPower_twoRow_gram hq0]

theorem diagonal_compression_above_four {p : ℝ} (hp : 4 ≤ p)
    (z : Fin 2 → J → D → ℂ) :
    schattenNorm p (diagonalBlockMatrix z) ≤ schattenNorm p (compression p z) := by
  unfold schattenNorm
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (diagonal_compression_above_four_power hp z) (by positivity)

end

end ResearchMain.DiagonalSchatten
