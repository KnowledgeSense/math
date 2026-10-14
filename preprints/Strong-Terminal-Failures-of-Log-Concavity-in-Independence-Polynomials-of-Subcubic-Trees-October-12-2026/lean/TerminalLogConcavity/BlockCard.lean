import TerminalLogConcavity.ScaledBlock

namespace TerminalLogConcavity
set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem Block.card_leaf : Fintype.card Block.leaf.Vertex = 1 := by
  simp [Block.Vertex, Block.children, ForestExpr.Vertex]

set_option backward.isDefEq.respectTransparency false in
theorem Block.card_binary (a b : Block) :
    Fintype.card (Block.binary a b).Vertex = Fintype.card a.Vertex + Fintype.card b.Vertex + 3 := by
  simp [Block.Vertex, Block.children, ForestExpr.Vertex, Fintype.card_sum]
  omega

theorem Block.balanced_card (t : ℕ) :
    Fintype.card (balanced t).Vertex + 3 = 4 * 2 ^ t := by
  induction t with
  | zero => simp [balanced, Vertex, children, ForestExpr.Vertex]
  | succ t ih => rw [balanced, card_binary, pow_succ]; omega

theorem Block.scaled_card (t : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    Fintype.card (scaled t p).Vertex + 3 = 4 * 2 ^ t * p := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases he : p = 1
    · subst p; simpa using balanced_card t
    · have hp2 : 2 ≤ p := by omega
      rw [scaled_binary t hp2, card_binary]
      have hl := ih (p / 2) (by omega) (by omega)
      have hr := ih ((p + 1) / 2) (by omega) (by omega)
      have hs : p / 2 + (p + 1) / 2 = p := by omega
      nlinarith

end TerminalLogConcavity
