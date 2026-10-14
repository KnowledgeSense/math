import SphericalTreeFailures.Definitions

namespace SphericalTreeFailures
set_option backward.isDefEq.respectTransparency false

theorem pendantPath_card (n : ℕ) : Fintype.card (pendantPath n).Vertex = n := by
  induction n with
  | zero => simp [pendantPath, ForestExpr.Vertex]
  | succ n ih => simpa [pendantPath, ForestExpr.Vertex] using ih

theorem sphericalTree_card (m n : ℕ) :
    Fintype.card (sphericalTree m n).Vertex + 1 = (n + 2) * 2 ^ m := by
  induction m with
  | zero => simp [sphericalTree, pendantPath_card]
  | succ m ih =>
    simp only [sphericalTree, ForestExpr.Vertex, Fintype.card_option, Fintype.card_sum]
    rw [pow_succ, ← Nat.mul_assoc]
    omega

theorem sphericalTree_isTree (m n : ℕ) : (sphericalTree m n).graph.IsTree := by
  cases m with
  | zero => exact (pendantPath n).root_graph_isTree
  | succ m => exact ((sphericalTree m n).union (sphericalTree m n)).root_graph_isTree

theorem pendantPath_rootCount (n : ℕ) : (pendantPath n).rootCount ≤ 1 := by
  cases n <;> simp [pendantPath]

theorem pendantPath_attachable (n : ℕ) : (pendantPath n).Attachable := by
  induction n with
  | zero => intro v; exact v.elim
  | succ n ih => exact ih.root ((pendantPath_rootCount n).trans (by decide))

theorem sphericalTree_rootCount (m n : ℕ) : (sphericalTree m n).rootCount = 1 := by
  cases m <;> simp [sphericalTree, pendantPath]

theorem sphericalTree_attachable (m n : ℕ) : (sphericalTree m n).Attachable := by
  induction m with
  | zero => exact pendantPath_attachable (n + 1)
  | succ m ih =>
    apply (ih.union ih).root
    simp [sphericalTree_rootCount]

theorem sphericalTree_subcubic (m n : ℕ) (v : (sphericalTree m n).Vertex) :
    ((sphericalTree m n).graph.neighborSet v).ncard ≤ 3 :=
  (sphericalTree_attachable m n).subcubic v

end SphericalTreeFailures
