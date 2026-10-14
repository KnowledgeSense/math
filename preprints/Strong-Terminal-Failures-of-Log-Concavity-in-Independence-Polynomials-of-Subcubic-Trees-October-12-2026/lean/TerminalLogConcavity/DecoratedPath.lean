import TerminalLogConcavity.Interface

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

/-- A rooted gap-one tree that can be attached to one vertex of a skeleton. -/
structure Decoration where
  children : ForestExpr
  gap : flag children = false
  attachable : children.root.Attachable

abbrev Decoration.forest (D : Decoration) : ForestExpr := .root D.children
noncomputable def Decoration.A (D : Decoration) : ℕ[X] :=
  reflect D.forest.alpha D.forest.polynomials.1
noncomputable def Decoration.B (D : Decoration) : ℕ[X] :=
  reflect D.children.alpha D.children.polynomials.1

def Block.decoration (b : Block) : Decoration :=
  ⟨b.children, b.children_flag, b.attachable⟩
def interfaceDecoration (p m : Block) : Decoration :=
  ⟨interfaceChildren p m, interfaceChildren_flag p m, interface_attachable p m⟩

@[simp] theorem Block.decoration_A (b : Block) : b.decoration.A = b.A := by
  change reflect b.toForest.alpha b.P = b.A
  rw [b.toForest_alpha]
  exact b.reversal.1
@[simp] theorem Block.decoration_B (b : Block) : b.decoration.B = b.B := by
  have he : b.children.alpha = b.rank - 1 := by have := b.children_alpha; omega
  simpa [Decoration.B, Block.decoration, he, Block.Q] using b.reversal.2
@[simp] theorem interfaceDecoration_A (p m : Block) : (interfaceDecoration p m).A = interfaceA p m := by
  rw [interfaceA_graph, ForestExpr.graph_alpha, ForestExpr.graph_polynomial]
  rfl
@[simp] theorem interfaceDecoration_B (p m : Block) : (interfaceDecoration p m).B = interfaceB p m := by
  rw [interfaceB_graph, ForestExpr.graph_alpha, ForestExpr.root_deleted_polynomial]
  simp [Decoration.B, interfaceDecoration, interfaceForest_alpha]

/-- A path skeleton with one specified rooted decoration at each skeleton vertex. -/
def decoratedPath : List Decoration → ForestExpr
  | [] => .empty
  | D :: ds => .root (.union D.forest (decoratedPath ds))

@[simp] theorem decoratedPath_flag (ds : List Decoration) : flag (decoratedPath ds) = false := by
  cases ds with
  | nil => rfl
  | cons D ds => simp [decoratedPath, Decoration.forest, flag, D.gap]

@[simp] theorem decoratedPath_alpha (ds : List Decoration) :
    (decoratedPath ds).alpha = (ds.map (fun D => D.forest.alpha)).sum := by
  induction ds with
  | nil => rfl
  | cons D ds ih => simp [decoratedPath, ForestExpr.alpha, Decoration.forest, flag, D.gap, ih]

@[simp] theorem decoratedPath_rootCount_le (ds : List Decoration) : (decoratedPath ds).rootCount ≤ 1 := by
  cases ds <;> simp [decoratedPath]

theorem decoratedPath_attachable (ds : List Decoration) : (decoratedPath ds).Attachable := by
  induction ds with
  | nil => intro v; exact v.elim
  | cons D ds ih =>
    apply (D.attachable.union ih).root
    rw [ForestExpr.rootCount_union]
    have := decoratedPath_rootCount_le ds
    simpa using Nat.add_le_add_left this 1

theorem decoratedPath_isTree (D : Decoration) (ds : List Decoration) :
    (decoratedPath (D :: ds)).graph.IsTree :=
  (ForestExpr.union D.forest (decoratedPath ds)).root_graph_isTree

theorem decoratedPath_subcubic (ds : List Decoration) (v : (decoratedPath ds).Vertex) :
    ((decoratedPath ds).graph.neighborSet v).ncard ≤ 3 :=
  (decoratedPath_attachable ds).subcubic v

/-- Independent-set state sum: first entry allows the first site, second forbids it. -/
noncomputable def pathStateSum : List Decoration → ℕ[X] × ℕ[X]
  | [] => (1, 1)
  | D :: ds =>
    (D.A * (pathStateSum ds).1 + D.B * (pathStateSum ds).2,
     D.A * (pathStateSum ds).1)

theorem ForestExpr.second_polynomial_degree (F : ForestExpr) :
    F.polynomials.2.natDegree ≤ F.alpha := by
  obtain ⟨rs, h, _⟩ := F.realization
  rw [← (h.polynomials_eq F.graph).2, ← h.alpha_eq F.graph]
  exact (independencePolynomial_natDegree_le _ _).trans
    (independenceNumber_mono _ Finset.sdiff_subset)

/-- The state recursion is the exact reversal of the finite graph counting polynomial. -/
theorem decoratedPath_reversal (ds : List Decoration) :
    reflect (decoratedPath ds).alpha (decoratedPath ds).polynomials.1 = (pathStateSum ds).1 ∧
    reflect (decoratedPath ds).alpha (decoratedPath ds).polynomials.2 = (pathStateSum ds).2 := by
  induction ds with
  | nil => simp [decoratedPath, pathStateSum, ForestExpr.polynomials, ForestExpr.alpha, reflect_one]
  | cons D ds ih =>
    have hd : D.forest.alpha = D.children.alpha + 1 := by
      simp [ForestExpr.alpha, D.gap]
    have halpha : (decoratedPath (D :: ds)).alpha = D.forest.alpha + (decoratedPath ds).alpha := by
      simp only [decoratedPath_alpha, List.map_cons, List.sum_cons]
    have hq : (D.children.polynomials.1 * (decoratedPath ds).polynomials.2).natDegree ≤
        D.children.alpha + (decoratedPath ds).alpha :=
      (natDegree_mul_le ..).trans
        (Nat.add_le_add D.children.polynomial_degree (decoratedPath ds).second_polynomial_degree)
    rw [halpha]
    constructor
    · change reflect (D.forest.alpha + (decoratedPath ds).alpha)
        (D.forest.polynomials.1 * (decoratedPath ds).polynomials.1 +
          X * (D.children.polynomials.1 * (decoratedPath ds).polynomials.2)) = _
      rw [reflect_add, reflect_mul _ _ D.forest.polynomial_degree (decoratedPath ds).polynomial_degree, ih.1]
      have hr : D.forest.alpha + (decoratedPath ds).alpha =
          (D.children.alpha + (decoratedPath ds).alpha) + 1 := by omega
      rw [hr, reflect_X_mul _ _ hq,
        reflect_mul _ _ D.children.polynomial_degree (decoratedPath ds).second_polynomial_degree, ih.2]
      rfl
    · change reflect (D.forest.alpha + (decoratedPath ds).alpha)
        (D.forest.polynomials.1 * (decoratedPath ds).polynomials.1) = _
      rw [reflect_mul _ _ D.forest.polynomial_degree (decoratedPath ds).polynomial_degree, ih.1]
      rfl

theorem pathStateSum_graph (ds : List Decoration) :
    (pathStateSum ds).1 = reflect (decoratedPath ds).graph.indepNum
      (independencePolynomial (decoratedPath ds).graph Finset.univ) := by
  rw [ForestExpr.graph_alpha, ForestExpr.graph_polynomial]
  exact (decoratedPath_reversal ds).1.symm

end TerminalLogConcavity
