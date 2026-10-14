import SphericalTreeFailures.GraphConstruction

set_option backward.isDefEq.respectTransparency false

namespace SphericalTreeFailures
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def ForestExpr.rootCount (A : ForestExpr) : ℕ := by
  classical
  exact ∑ v : A.Vertex, if A.IsRoot v then 1 else 0

noncomputable def ForestExpr.degreeCount (A : ForestExpr) (v : A.Vertex) : ℕ := by
  classical
  exact ∑ w : A.Vertex, if A.Adj v w then 1 else 0

@[simp] theorem ForestExpr.rootCount_empty : ForestExpr.empty.rootCount = 0 := by
  simp [rootCount]
@[simp] theorem ForestExpr.rootCount_union (A B : ForestExpr) :
    (ForestExpr.union A B).rootCount = A.rootCount + B.rootCount := by
  simp only [rootCount, Fintype.sum_sum_type, IsRoot]
@[simp] theorem ForestExpr.rootCount_root (A : ForestExpr) :
    (ForestExpr.root A).rootCount = 1 := by
  simp only [rootCount, Fintype.sum_option, IsRoot, ite_true, ite_false, sum_const_zero, add_zero]

@[simp] theorem ForestExpr.degreeCount_inl (A B : ForestExpr) (v : A.Vertex) :
    (ForestExpr.union A B).degreeCount (.inl v) = A.degreeCount v := by
  simp only [degreeCount, Fintype.sum_sum_type, Adj, ite_false, sum_const_zero, add_zero]
@[simp] theorem ForestExpr.degreeCount_inr (A B : ForestExpr) (v : B.Vertex) :
    (ForestExpr.union A B).degreeCount (.inr v) = B.degreeCount v := by
  simp only [degreeCount, Fintype.sum_sum_type, Adj, ite_false, sum_const_zero, zero_add]
@[simp] theorem ForestExpr.degreeCount_none (A : ForestExpr) :
    (ForestExpr.root A).degreeCount none = A.rootCount := by
  simp only [degreeCount, rootCount, Fintype.sum_option, Adj, ite_false, zero_add]
@[simp] theorem ForestExpr.degreeCount_some (A : ForestExpr) (v : A.Vertex) :
    (ForestExpr.root A).degreeCount (some v) = A.degreeCount v +
      (if A.IsRoot v then 1 else 0) := by
  classical
  simp only [degreeCount, Fintype.sum_option, Adj, Nat.add_comm]

/-- Degree count agrees with the cardinality of the actual graph's neighbor set. -/
theorem ForestExpr.degreeCount_eq (A : ForestExpr) (v : A.Vertex) :
    A.degreeCount v = (A.graph.neighborSet v).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have he : (A.graph.neighborSet v).toFinset = univ.filter (A.Adj v) := by
    ext w
    simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet, mem_filter, mem_univ, true_and]
    rfl
  rw [he, card_filter]
  rfl

/-- A forest whose roots have one spare degree for attachment to a parent. -/
def ForestExpr.Attachable (A : ForestExpr) : Prop :=
  ∀ v : A.Vertex, A.degreeCount v + (if A.IsRoot v then 1 else 0) ≤ 3

theorem ForestExpr.Attachable.union {A B : ForestExpr} (ha : A.Attachable) (hb : B.Attachable) :
    (A.union B).Attachable := by
  intro v
  cases v with
  | inl v => rw [ForestExpr.degreeCount_inl]; exact ha v
  | inr v => rw [ForestExpr.degreeCount_inr]; exact hb v

theorem ForestExpr.Attachable.root {A : ForestExpr} (ha : A.Attachable) (hr : A.rootCount ≤ 2) :
    A.root.Attachable := by
  intro v
  cases v with
  | none => rw [ForestExpr.degreeCount_none]; simpa [ForestExpr.IsRoot] using Nat.add_le_add_right hr 1
  | some v => rw [ForestExpr.degreeCount_some]; simpa [ForestExpr.IsRoot] using ha v

theorem ForestExpr.Attachable.subcubic {A : ForestExpr} (ha : A.Attachable) (v : A.Vertex) :
    (A.graph.neighborSet v).ncard ≤ 3 := by
  rw [← A.degreeCount_eq]
  exact (Nat.le_add_right _ _).trans (ha v)


end SphericalTreeFailures
