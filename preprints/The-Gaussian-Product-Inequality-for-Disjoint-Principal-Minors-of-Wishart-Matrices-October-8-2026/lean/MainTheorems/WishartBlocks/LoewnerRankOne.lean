import MainTheorems.WishartBlocks.NoncentralDeterminantResponse

namespace ResearchMain.WishartBlocks

open Matrix
open scoped BigOperators MatrixOrder

noncomputable def matrixColumn {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (R.transpose i)

theorem matrix_column_gram_sum {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ) :
    (∑ i, Matrix.vecMulVec (fun j => matrixColumn R i j) (fun j => matrixColumn R i j)) =
      R * R.transpose := by
  simpa only [matrixColumn, meanRowGram, Matrix.transpose_transpose] using matrix_rows_gram R.transpose

theorem monotoneOn_positiveDefinite_of_rankOne {k : ℕ}
    {G : Matrix (Fin k) (Fin k) ℝ → ℝ}
    (hG : ∀ W, W.PosDef → ∀ u : EuclideanSpace ℝ (Fin k),
      G W ≤ G (W + Matrix.vecMulVec (fun i => u i) (fun i => u i))) :
    MonotoneOn G {W | W.PosDef} := by
  classical
  intro W hW V hV hWV
  have hD : (V - W).PosSemidef := hWV
  let R := CFC.sqrt (V - W)
  let A := fun i : Fin k => Matrix.vecMulVec
    (fun j => matrixColumn R i j) (fun j => matrixColumn R i j)
  have hA : ∀ i, (A i).PosSemidef := by
    intro i
    simpa only [A, star_trivial] using Matrix.posSemidef_vecMulVec_self_star
      (fun j => matrixColumn R i j)
  have hsum : (∑ i, A i) = V - W := by
    rw [matrix_column_gram_sum]
    have hRt : R.transpose = R := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg (V - W)).posSemidef.1.eq
    rw [hRt]
    exact CFC.sqrt_mul_sqrt_self (V - W) hD.nonneg
  have hi : ∀ s : Finset (Fin k), G W ≤ G (W + ∑ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        have hsPSD : (∑ j ∈ s, A j).PosSemidef :=
          Matrix.posSemidef_sum s fun j _ => hA j
        have h := hG (W + ∑ j ∈ s, A j) (hW.add_posSemidef hsPSD) (matrixColumn R i)
        apply ih.trans
        simpa only [Finset.sum_insert his, add_assoc, add_left_comm, add_comm, A] using h
  have h := hi Finset.univ
  change G W ≤ G (W + ∑ i, A i) at h
  have he : W + (V - W) = V := by abel
  rw [hsum, he] at h
  exact h

theorem noncentralDeterminantResponse_monotone {p n : ℕ} {α b : ℝ}
    (hα : (p : ℝ) - 1 < α - ((n + 1 : ℕ) : ℝ)) (hb : 0 ≤ b)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (K : Matrix (Fin (n + 1)) (Fin p) ℝ) :
    MonotoneOn (noncentralDeterminantResponse α S K b) {W | W.PosDef} := by
  apply monotoneOn_positiveDefinite_of_rankOne
  intro W hW u
  simpa only [one_smul] using noncentralDeterminantResponse_rankOne hα hb
    (by norm_num : (0 : ℝ) ≤ 1) hS K hW u

end ResearchMain.WishartBlocks
