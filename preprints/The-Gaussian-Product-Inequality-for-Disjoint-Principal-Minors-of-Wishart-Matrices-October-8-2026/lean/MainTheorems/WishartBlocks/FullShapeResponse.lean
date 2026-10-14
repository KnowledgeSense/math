import MainTheorems.WishartBlocks.RegressionProductIdentity

namespace ResearchMain.WishartBlocks

open Matrix
open scoped MatrixOrder

namespace BlockPartition

theorem noncentralProductResponse_full_shape_monotone {m n d : ℕ}
    (P : BlockPartition m (d + 2)) (ν : Fin (d + 2) → ℝ) (hν : ∀ j, 0 ≤ ν j)
    {α : ℝ} (hα : (((n + 1) + m : ℕ) : ℝ) - 1 < α)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    (K : Matrix (Fin (n + 1)) (Fin m) ℝ) :
    MonotoneOn (P.noncentralProductResponse α S K ν) {W | W.PosDef} := by
  have hr : (m : ℝ) - 1 < α - ((n + 1 : ℕ) : ℝ) := by push_cast at hα ⊢; linarith
  have hq : (m : ℝ) < α - (n : ℝ) := by push_cast at hα; linarith
  have hm : 2 ≤ m := by
    have hs := P.size_pos (0 : Fin (d + 2))
    have hd := P.other_block_dimension (0 : Fin (d + 2))
    omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq₁ : 1 < α - (n : ℝ) := by linarith
  have hqB : ∀ j, (P.size j : ℝ) + 1 ≤ α - (n : ℝ) := by
    intro j
    have hs : (P.size j : ℝ) + 1 ≤ m := by exact_mod_cast P.other_block_dimension j
    exact hs.trans hq.le
  exact P.noncentralProductResponse_monotone ν hν hr hq₁ hqB hS K

end BlockPartition

theorem noncentralDeterminantResponse_full_shape_monotone {m n : ℕ} {α b : ℝ}
    (hα : (((n + 1) + m : ℕ) : ℝ) - 1 < α) (hb : 0 ≤ b)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosDef)
    (K : Matrix (Fin (n + 1)) (Fin m) ℝ) :
    MonotoneOn (noncentralDeterminantResponse α S K b) {W | W.PosDef} := by
  apply noncentralDeterminantResponse_monotone _ hb hS K
  push_cast at hα ⊢
  linarith

end ResearchMain.WishartBlocks
