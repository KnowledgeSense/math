import TerminalLogConcavity.Block
import TerminalLogConcavity.NodeEnvelope
import TerminalLogConcavity.LinearProduct

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def Block.d (b : Block) : ℕ := b.B.coeff 0

@[simp] theorem Block.d_leaf : Block.leaf.d = 1 := by simp [Block.d]

@[simp] theorem Block.d_binary (a b : Block) :
    (Block.binary a b).d = (1 + a.d) * (1 + b.d) := by
  simp [Block.d, mul_coeff_zero]

theorem Block.d_pos (b : Block) : 0 < b.d := by
  cases b <;> simp

@[simp] theorem Block.d_balanced (t : ℕ) : (Block.balanced t).d = amplifier t :=
  Block.balanced_B_constant t

theorem Block.one_le_A (b : Block) : CoeffLE 1 b.A := by
  simpa using CoeffLE.constant_le b.A

theorem Block.d_le_B (b : Block) : CoeffLE (C b.d) b.B :=
  CoeffLE.constant_le b.B

noncomputable def Block.nodeWeights : Block → List ℕ
  | .leaf => [1]
  | .binary a b => (Block.binary a b).d :: (a.nodeWeights ++ b.nodeWeights)

theorem Block.node_envelope (b : Block) :
    CoeffLE b.A (linearProduct b.nodeWeights) ∧
      CoeffLE b.B (C b.d * linearProduct b.nodeWeights) := by
  induction b with
  | leaf =>
    constructor
    · simp only [A_leaf, nodeWeights, linearProduct, map_one, one_mul, mul_one]
      exact CoeffLE.refl _
    · simpa [nodeWeights, linearProduct] using CoeffLE.le_add_right (1 : ℕ[X]) X
  | binary a b ha hb =>
    have h := node_envelope_step ha.1 hb.1 ha.2 hb.2
    simpa only [A_binary, B_binary, nodeWeights, linearProduct, linearProduct_append,
      d_binary, mul_comm (1 + C ((1 + a.d) * (1 + b.d)) * X)] using h

theorem Block.A_coeff_le (b : Block) (n : ℕ) : b.A.coeff n ≤ b.nodeWeights.sum ^ n :=
  (b.node_envelope.1 n).trans (linearProduct_coeff_le _ _)

theorem Block.B_coeff_le (b : Block) (n : ℕ) :
    b.B.coeff n ≤ b.d * b.nodeWeights.sum ^ n := by
  have h := b.node_envelope.2 n
  rw [coeff_C_mul] at h
  exact h.trans (Nat.mul_le_mul_left _ (linearProduct_coeff_le _ _))

theorem Block.nodeWeights_sum_le (b : Block) :
    b.nodeWeights.sum ≤ b.nodeWeights.length * b.d := by
  induction b with
  | leaf => simp [nodeWeights]
  | binary a b ha hb =>
    have hda : a.d ≤ (1 + a.d) * (1 + b.d) := by nlinarith
    have hdb : b.d ≤ (1 + a.d) * (1 + b.d) := by nlinarith
    have hma := Nat.mul_le_mul_left a.nodeWeights.length hda
    have hmb := Nat.mul_le_mul_left b.nodeWeights.length hdb
    simp only [nodeWeights, List.sum_cons, List.sum_append, List.length_cons,
      List.length_append, d_binary]
    nlinarith

set_option backward.isDefEq.respectTransparency false in
theorem Block.nodeWeights_length_le_card (b : Block) :
    b.nodeWeights.length ≤ Fintype.card b.Vertex := by
  induction b with
  | leaf => simp [nodeWeights, Vertex, children, ForestExpr.Vertex]
  | binary a b ha hb =>
    simp only [nodeWeights, List.length_cons, List.length_append]
    simp only [Vertex, children, ForestExpr.Vertex, Fintype.card_option,
      Fintype.card_sum] at ha hb ⊢
    omega

theorem Block.nodeWeights_sum_le_card_mul (b : Block) :
    b.nodeWeights.sum ≤ Fintype.card b.Vertex * b.d :=
  b.nodeWeights_sum_le.trans (Nat.mul_le_mul_right b.d b.nodeWeights_length_le_card)

end TerminalLogConcavity
