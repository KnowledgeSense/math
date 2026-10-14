import TerminalLogConcavity.BlockReversal
import TerminalLogConcavity.GraphDegree

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

/-- The three new vertices of the interface above blocks p,m,m. -/
def interfaceChildren (p m : Block) : ForestExpr :=
  .root (.union p.toForest (.root (.union m.toForest m.toForest)))
abbrev interfaceForest (p m : Block) : ForestExpr := .root (interfaceChildren p m)

@[simp] theorem interfaceChildren_flag (p m : Block) : flag (interfaceChildren p m) = false := by
  simp [interfaceChildren, Block.toForest, flag]

@[simp] theorem interfaceChildren_alpha (p m : Block) :
    (interfaceChildren p m).alpha = p.rank + (m.rank + m.rank) := by
  simp [interfaceChildren, ForestExpr.alpha, flag]

@[simp] theorem interfaceForest_alpha (p m : Block) :
    (interfaceForest p m).alpha = p.rank + (m.rank + m.rank) + 1 := by
  simp [ForestExpr.alpha]

theorem interface_isTree (p m : Block) : (interfaceForest p m).graph.IsTree :=
  (interfaceChildren p m).root_graph_isTree

noncomputable def interfaceE (p m : Block) : ℕ[X] := p.A * (m.A ^ 2 + X * m.B ^ 2)
noncomputable def interfaceO (p m : Block) : ℕ[X] := p.B * m.A ^ 2
noncomputable def interfaceA (p m : Block) : ℕ[X] := interfaceE p m + X * (interfaceE p m + interfaceO p m)
noncomputable def interfaceB (p m : Block) : ℕ[X] := interfaceE p m + interfaceO p m

@[simp] theorem interfaceA_constant (p m : Block) : (interfaceA p m).coeff 0 = 1 := by
  simp [interfaceA, interfaceE, mul_coeff_zero, pow_two]

private theorem reflect_inner (m : Block) :
    reflect (m.rank + m.rank) (m.P ^ 2 + X * m.Q ^ 2) = m.A ^ 2 + X * m.B ^ 2 := by
  have hq : (m.Q * m.Q).natDegree ≤ (m.rank - 1) + (m.rank - 1) :=
    (natDegree_mul_le ..).trans (Nat.add_le_add m.Q_degree m.Q_degree)
  have hr : m.rank + m.rank = ((m.rank - 1) + (m.rank - 1) + 1) + 1 := by
    have := m.rank_pos; omega
  simp only [pow_two]
  rw [reflect_add, reflect_mul _ _ m.P_degree m.P_degree, m.reversal.1]
  congr 1
  rw [hr, reflect_X_mul _ _ (hq.trans (Nat.le_succ _)),
    reflect_raise _ _ hq, reflect_mul _ _ m.Q_degree m.Q_degree, m.reversal.2]

private theorem inner_degree (m : Block) :
    (m.P ^ 2 + X * m.Q ^ 2).natDegree ≤ m.rank + m.rank := by
  have h := (ForestExpr.root (.union m.toForest m.toForest)).polynomial_degree
  simpa [ForestExpr.polynomials, ForestExpr.alpha, flag, Block.P, Block.Q, pow_two] using h

private theorem children_polynomial (p m : Block) :
    (interfaceChildren p m).polynomials.1 =
      p.P * (m.P ^ 2 + X * m.Q ^ 2) + X * (p.Q * m.P ^ 2) := by
  simp only [interfaceChildren, ForestExpr.polynomials, Block.P, Block.Q,
    Block.toForest, pow_two]

private theorem children_reversal (p m : Block) :
    reflect (p.rank + (m.rank + m.rank)) (interfaceChildren p m).polynomials.1 = interfaceB p m := by
  have hq : (p.Q * (m.P * m.P)).natDegree ≤ (p.rank - 1) + (m.rank + m.rank) :=
    (natDegree_mul_le ..).trans (Nat.add_le_add p.Q_degree
      ((natDegree_mul_le ..).trans (Nat.add_le_add m.P_degree m.P_degree)))
  rw [children_polynomial, reflect_add,
    reflect_mul _ _ p.P_degree (inner_degree m), p.reversal.1, reflect_inner]
  have hr : p.rank + (m.rank + m.rank) = ((p.rank - 1) + (m.rank + m.rank)) + 1 := by
    have := p.rank_pos; omega
  simp only [pow_two]
  rw [hr, reflect_X_mul _ _ hq,
    reflect_mul _ _ p.Q_degree ((natDegree_mul_le ..).trans (Nat.add_le_add m.P_degree m.P_degree)),
    reflect_mul _ _ m.P_degree m.P_degree, p.reversal.2, m.reversal.1]
  simp only [interfaceB, interfaceE, interfaceO, pow_two]

/-- Exact reversed polynomial of the actual interface tree. -/
theorem interfaceA_graph (p m : Block) :
    interfaceA p m = reflect (interfaceForest p m).graph.indepNum
      (independencePolynomial (interfaceForest p m).graph Finset.univ) := by
  rw [ForestExpr.graph_alpha, ForestExpr.graph_polynomial, interfaceForest_alpha]
  change interfaceA p m = reflect (p.rank + (m.rank + m.rank) + 1)
    ((interfaceChildren p m).polynomials.1 + X * (interfaceChildren p m).polynomials.2)
  rw [reflect_add, reflect_raise _ _ (by simpa using (interfaceChildren p m).polynomial_degree), children_reversal]
  have he : (interfaceChildren p m).polynomials.2 = p.P * (m.P ^ 2 + X * m.Q ^ 2) := by
    simp only [interfaceChildren, ForestExpr.polynomials, Block.P, Block.Q, Block.toForest, pow_two]
  rw [he, reflect_X_mul _ _ ((natDegree_mul_le ..).trans (Nat.add_le_add p.P_degree (inner_degree m))),
    reflect_mul _ _ p.P_degree (inner_degree m), p.reversal.1, reflect_inner]
  simp only [interfaceA, interfaceB, interfaceE]
  ring

theorem interfaceB_graph (p m : Block) :
    interfaceB p m = reflect ((interfaceForest p m).graph.indepNum - 1)
      (independencePolynomial (interfaceForest p m).graph (Finset.univ.erase none)) := by
  rw [ForestExpr.graph_alpha, interfaceForest_alpha, Nat.add_sub_cancel,
    ForestExpr.root_deleted_polynomial]
  exact (children_reversal p m).symm

theorem interface_attachable (p m : Block) : (interfaceForest p m).Attachable := by
  apply ForestExpr.Attachable.root
  · apply ForestExpr.Attachable.root
    · apply ForestExpr.Attachable.union p.attachable
      apply ForestExpr.Attachable.root (m.attachable.union m.attachable)
      rw [ForestExpr.rootCount_union]
      simp
    · rw [ForestExpr.rootCount_union]
      simp
  · simp [interfaceChildren]

theorem interface_subcubic (p m : Block) (v : (interfaceForest p m).Vertex) :
    ((interfaceForest p m).graph.neighborSet v).ncard ≤ 3 :=
  (interface_attachable p m).subcubic v

end TerminalLogConcavity
