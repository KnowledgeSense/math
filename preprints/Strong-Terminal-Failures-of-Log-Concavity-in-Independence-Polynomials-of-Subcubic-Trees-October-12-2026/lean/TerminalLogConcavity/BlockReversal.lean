import TerminalLogConcavity.Block

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

theorem reflect_raise (p : ℕ[X]) (n : ℕ) (h : p.natDegree ≤ n) :
    reflect (n + 1) p = X * reflect n p := by
  simpa [reflect_one, Nat.add_comm] using
    (reflect_mul (1 : ℕ[X]) p (F := 1) (G := n) (by simp) h)

theorem reflect_X_mul (p : ℕ[X]) (n : ℕ) (h : p.natDegree ≤ n) :
    reflect (n + 1) (X * p) = reflect n p := by
  simpa [Nat.add_comm] using
    (reflect_mul (X : ℕ[X]) p (F := 1) (G := n) (by simp) h)

theorem ForestExpr.polynomial_degree (A : ForestExpr) :
    A.polynomials.1.natDegree ≤ A.alpha := by
  obtain ⟨rs, h, _⟩ := A.realization
  rw [← A.graph_polynomial, ← h.alpha_eq A.graph]
  exact independencePolynomial_natDegree_le _ _

/-- Ordinary polynomial of the whole rooted block. -/
noncomputable def Block.P (b : Block) : ℕ[X] := b.toForest.polynomials.1
/-- Ordinary polynomial after removing the distinguished root. -/
noncomputable def Block.Q (b : Block) : ℕ[X] := b.children.polynomials.1

theorem Block.P_degree (b : Block) : b.P.natDegree ≤ b.rank := by
  simpa [P] using b.toForest.polynomial_degree

theorem Block.Q_degree (b : Block) : b.Q.natDegree ≤ b.rank - 1 := by
  have h := b.children.polynomial_degree
  have he := b.children_alpha
  change b.children.polynomials.1.natDegree ≤ _
  omega

@[simp] theorem Block.P_leaf : Block.leaf.P = 1 + X := by
  simp [P, children, ForestExpr.polynomials]
@[simp] theorem Block.Q_leaf : Block.leaf.Q = 1 := rfl

@[simp] theorem Block.P_binary (a b : Block) :
    (Block.binary a b).P = (a.P + X * a.Q) * (b.P + X * b.Q) + X * a.P * b.P := by
  simp only [P, Q, children, ForestExpr.polynomials]
  ring
@[simp] theorem Block.Q_binary (a b : Block) :
    (Block.binary a b).Q = (a.P + X * a.Q) * (b.P + X * b.Q) := rfl

private theorem Block.branch_degree (b : Block) :
    (b.P + X * b.Q).natDegree ≤ b.rank := by
  apply natDegree_add_le_of_degree_le
  · exact b.P_degree
  · exact (natDegree_mul_le ..).trans (by have := b.Q_degree; have := b.rank_pos; simp only [natDegree_X]; omega)

private theorem Block.reflect_branch (b : Block)
    (hP : reflect b.rank b.P = b.A) (hQ : reflect (b.rank - 1) b.Q = b.B) :
    reflect b.rank (b.P + X * b.Q) = b.A + b.B := by
  rw [reflect_add, hP]
  have hr : b.rank = (b.rank - 1) + 1 := by have := b.rank_pos; omega
  conv_lhs => arg 2; rw [hr, reflect_X_mul b.Q _ b.Q_degree, hQ]

/-- Both reversed polynomials are exactly reversals of the enumerated graph polynomials. -/
theorem Block.reversal (b : Block) :
    reflect b.rank b.P = b.A ∧ reflect (b.rank - 1) b.Q = b.B := by
  induction b with
  | leaf => simp [rank, reflect_add, reflect_one, add_comm]
  | binary a b ha hb =>
    have hprod : (a.P * b.P).natDegree ≤ a.rank + b.rank :=
      (natDegree_mul_le ..).trans (Nat.add_le_add a.P_degree b.P_degree)
    have hbranch : ((a.P + X * a.Q) * (b.P + X * b.Q)).natDegree ≤ a.rank + b.rank :=
      (natDegree_mul_le ..).trans (Nat.add_le_add a.branch_degree b.branch_degree)
    have hr : reflect (a.rank + b.rank) ((a.P + X * a.Q) * (b.P + X * b.Q)) =
        (a.A + a.B) * (b.A + b.B) := by
      rw [reflect_mul _ _ a.branch_degree b.branch_degree,
        a.reflect_branch ha.1 ha.2, b.reflect_branch hb.1 hb.2]
    constructor
    · rw [P_binary, rank, reflect_add]
      rw [reflect_raise _ _ hbranch, hr]
      rw [mul_assoc X a.P b.P, reflect_X_mul _ _ hprod,
        reflect_mul _ _ a.P_degree b.P_degree, ha.1, hb.1, A_binary]
      ring
    · simpa only [rank, Nat.add_sub_cancel, Q_binary, B_binary] using hr

theorem Block.A_graph (b : Block) :
    b.A = reflect b.graph.indepNum (independencePolynomial b.graph Finset.univ) := by
  rw [b.graph_indepNum]
  exact b.reversal.1.symm.trans (by rw [show independencePolynomial b.graph Finset.univ = b.P from b.toForest.graph_polynomial])

theorem Block.B_graph (b : Block) :
    b.B = reflect (b.graph.indepNum - 1)
      (independencePolynomial b.graph (Finset.univ.erase none)) := by
  rw [b.graph_indepNum, show independencePolynomial b.graph (Finset.univ.erase none) = b.Q from b.children.root_deleted_polynomial]
  exact b.reversal.2.symm

end TerminalLogConcavity
