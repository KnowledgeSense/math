import HardCoreActivityThreshold.ForestExpectation

/-! Boundary perturbations propagate through the actual hard-core tree law. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

theorem forestMarginal_union_left (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (v : A.Vertex) :
    forestMarginal (A.union B) activity ha parent (.inl v) =
      forestMarginal A (fun v => activity (.inl v)) (fun v => ha (.inl v)) parent v := by
  have h := forestLaw_union_expectation A B activity ha parent (boolOccupation v) (fun _ => 1)
  unfold forestMarginal
  simp only [FiniteLaw.expectation_const, mul_one] at h
  convert h using 1
  congr 1

theorem forestMarginal_union_right (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (v : B.Vertex) :
    forestMarginal (A.union B) activity ha parent (.inr v) =
      forestMarginal B (fun v => activity (.inr v)) (fun v => ha (.inr v)) parent v := by
  have h := forestLaw_union_expectation A B activity ha parent (fun _ => 1) (boolOccupation v)
  unfold forestMarginal
  simp only [FiniteLaw.expectation_const, one_mul] at h
  convert h using 1
  congr 1

noncomputable def parentEffect (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : ℝ :=
  forestMarginal A activity ha true v - forestMarginal A activity ha false v

theorem parentEffect_root (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    parentEffect A.root activity ha none = -downwardOccupation A activity := by
  simp [parentEffect, forestMarginal_root_free]

theorem parentEffect_child (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    parentEffect A.root activity ha (some v) = -downwardOccupation A activity *
      parentEffect A (fun v => activity (some v)) (fun v => ha (some v)) v := by
  unfold parentEffect
  rw [forestMarginal_child_free, forestMarginal_child_forced]
  ring

noncomputable def RegularMessages (p : ℝ) : (A : ForestExpr) → (A.Vertex → ℝ) → Prop
  | .empty, _ => True
  | .union A B, activity => RegularMessages p A (fun v => activity (.inl v)) ∧
      RegularMessages p B (fun v => activity (.inr v))
  | .root A, activity => downwardOccupation A activity = p ∧
      RegularMessages p A (fun v => activity (some v))

/-- The boundary response is an exact path product, here specialized to a constant message. -/
theorem regular_parentEffect (p : ℝ) (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (hreg : RegularMessages p A activity) (v : A.Vertex) :
    parentEffect A activity ha v = (-p) ^ (A.depth v + 1) := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v
    · simp only [parentEffect, forestMarginal_union_left]
      exact ihA _ _ hreg.1 _
    · simp only [parentEffect, forestMarginal_union_right]
      exact ihB _ _ hreg.2 _
  | root A ih =>
    cases v with
    | none => rw [parentEffect_root, hreg.1]; simp [ForestExpr.depth]
    | some v =>
      rw [parentEffect_child, hreg.1, ih _ _ hreg.2 v]
      simp only [ForestExpr.depth, pow_succ]
      ring

/-- The invariant occupation probability of the hard-core two-state edge transition. -/
noncomputable def stationaryOccupation (p : ℝ) : ℝ := p / (1+p)

theorem stationaryOccupation_identity (p : ℝ) (hp : 0 ≤ p) :
    p * (1 - stationaryOccupation p) = stationaryOccupation p := by
  unfold stationaryOccupation
  have h : 1+p ≠ 0 := by positivity
  field_simp
  ring

theorem regular_stationary_marginal (p : ℝ) (hp : 0 ≤ p) (A : ForestExpr)
    (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (hreg : RegularMessages p A activity) (v : A.Vertex) :
    forestMarginal A activity ha false v + stationaryOccupation p * parentEffect A activity ha v =
      stationaryOccupation p := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v
    · simp only [parentEffect, forestMarginal_union_left]
      exact ihA _ _ hreg.1 _
    · simp only [parentEffect, forestMarginal_union_right]
      exact ihB _ _ hreg.2 _
  | root A ih =>
    cases v with
    | none =>
      rw [forestMarginal_root_free, parentEffect_root, hreg.1]
      nlinarith [stationaryOccupation_identity p hp]
    | some v =>
      rw [forestMarginal_child_free, parentEffect_child, hreg.1]
      have hi := ih (fun v => activity (some v)) (fun v => ha (some v)) hreg.2 v
      have he := stationaryOccupation_identity p hp
      calc
        _ = forestMarginal A (fun v => activity (some v)) (fun v => ha (some v)) false v +
            (p * (1 - stationaryOccupation p)) *
              parentEffect A (fun v => activity (some v)) (fun v => ha (some v)) v := by
                unfold parentEffect
                ring
        _ = stationaryOccupation p := by rw [he]; exact hi

end HardCoreActivityThreshold
