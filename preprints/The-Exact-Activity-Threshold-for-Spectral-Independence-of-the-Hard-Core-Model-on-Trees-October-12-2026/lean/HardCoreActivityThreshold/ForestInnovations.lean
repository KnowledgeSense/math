import HardCoreActivityThreshold.ForestExpectation

/-! Orthogonal innovations of the actual finite hard-core broadcast law. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

theorem forestLaw_union_expectation_left (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (f : (A.Vertex → Bool) → ℝ) :
    (forestLaw (A.union B) activity ha parent).expectation (fun x => f (fun v => x (.inl v))) =
      (forestLaw A (fun v => activity (.inl v)) (fun v => ha (.inl v)) parent).expectation f := by
  simpa using forestLaw_union_expectation A B activity ha parent f (fun _ => 1)

theorem forestLaw_union_expectation_right (A B : ForestExpr) (activity : (A.union B).Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (f : (B.Vertex → Bool) → ℝ) :
    (forestLaw (A.union B) activity ha parent).expectation (fun x => f (fun v => x (.inr v))) =
      (forestLaw B (fun v => activity (.inr v)) (fun v => ha (.inr v)) parent).expectation f := by
  simpa using forestLaw_union_expectation A B activity ha parent (fun _ => 1) f

noncomputable def vertexMessage : (A : ForestExpr) → (A.Vertex → ℝ) → A.Vertex → ℝ
  | .empty, _, v => v.elim
  | .union A _, activity, .inl v => vertexMessage A (fun v => activity (.inl v)) v
  | .union _ B, activity, .inr v => vertexMessage B (fun v => activity (.inr v)) v
  | .root A, activity, none => downwardOccupation A activity
  | .root A, activity, some v => vertexMessage A (fun v => activity (some v)) v

/-- The occupation minus its exact conditional expectation given its parent. -/
noncomputable def innovation : (A : ForestExpr) → (A.Vertex → ℝ) → Bool → A.Vertex → (A.Vertex → Bool) → ℝ
  | .empty, _, _, v, _ => v.elim
  | .union A _, activity, parent, .inl v, x => innovation A (fun v => activity (.inl v)) parent v (fun v => x (.inl v))
  | .union _ B, activity, parent, .inr v, x => innovation B (fun v => activity (.inr v)) parent v (fun v => x (.inr v))
  | .root A, activity, parent, none, x => boolOccupation none x - if parent then 0 else downwardOccupation A activity
  | .root A, activity, _, some v, x => innovation A (fun v => activity (some v)) (x none) v (fun v => x (some v))

/-- Each innovation has zero mean, for either fixed external-parent state. -/
theorem innovation_mean (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (parent : Bool) (v : A.Vertex) :
    (forestLaw A activity ha parent).expectation (innovation A activity parent v) = 0 := by
  induction A generalizing parent with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v
    · change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => innovation A (fun v => activity (.inl v)) parent _ (fun v => x (.inl v))) = 0
      rw [forestLaw_union_expectation_left]
      exact ihA _ _ _ _
    · change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => innovation B (fun v => activity (.inr v)) parent _ (fun v => x (.inr v))) = 0
      rw [forestLaw_union_expectation_right]
      exact ihB _ _ _ _
  | root A ih =>
    cases parent
    · rw [forestLaw_root_free_expectation]
      cases v
      · simp [innovation, boolOccupation]
        ring
      · simp only [innovation, Option.elim_none, Option.elim_some]
        rw [ih _ _ false _, ih _ _ true _]
        ring
    · rw [forestLaw_root_forced_expectation]
      cases v
      · simp [innovation, boolOccupation]
      · simp only [innovation, Option.elim_none, Option.elim_some]
        exact ih _ _ false _

/-- Distinct innovations are orthogonal in the actual probability law. -/
theorem innovation_orthogonal (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (parent : Bool) (u v : A.Vertex) (hne : u ≠ v) :
    (forestLaw A activity ha parent).expectation
      (fun x => innovation A activity parent u x * innovation A activity parent v x) = 0 := by
  induction A generalizing parent with
  | empty => exact u.elim
  | union A B ihA ihB =>
    cases u <;> cases v
    · rename_i u v
      change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => (fun y => innovation A (fun v => activity (.inl v)) parent _ y *
          innovation A (fun v => activity (.inl v)) parent _ y) (fun v => x (.inl v))) = 0
      rw [forestLaw_union_expectation_left A B activity ha parent
        (fun y => innovation A (fun v => activity (.inl v)) parent u y *
          innovation A (fun v => activity (.inl v)) parent v y)]
      exact ihA _ _ _ _ _ (fun h => hne (congrArg Sum.inl h))
    · change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => innovation A (fun v => activity (.inl v)) parent _ (fun v => x (.inl v)) *
          innovation B (fun v => activity (.inr v)) parent _ (fun v => x (.inr v))) = 0
      rw [forestLaw_union_expectation, innovation_mean, innovation_mean]
      ring
    · simp_rw [mul_comm]
      change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => innovation A (fun v => activity (.inl v)) parent _ (fun v => x (.inl v)) *
          innovation B (fun v => activity (.inr v)) parent _ (fun v => x (.inr v))) = 0
      rw [forestLaw_union_expectation, innovation_mean, innovation_mean]
      ring
    · rename_i u v
      change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => (fun y => innovation B (fun v => activity (.inr v)) parent _ y *
          innovation B (fun v => activity (.inr v)) parent _ y) (fun v => x (.inr v))) = 0
      rw [forestLaw_union_expectation_right A B activity ha parent
        (fun y => innovation B (fun v => activity (.inr v)) parent u y *
          innovation B (fun v => activity (.inr v)) parent v y)]
      exact ihB _ _ _ _ _ (fun h => hne (congrArg Sum.inr h))
  | root A ih =>
    cases parent
    · rw [forestLaw_root_free_expectation]
      cases u <;> cases v
      · exact False.elim (hne rfl)
      · simp only [innovation, boolOccupation, Option.elim_none, Option.elim_some,
          Bool.false_eq_true, ↓reduceIte]
        rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_smul, innovation_mean, innovation_mean]
        ring
      · simp only [innovation, boolOccupation, Option.elim_none, Option.elim_some,
          Bool.false_eq_true, ↓reduceIte]
        simp_rw [mul_comm (innovation A _ _ _ _)]
        rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_smul, innovation_mean, innovation_mean]
        ring
      · simp only [innovation, Option.elim_none, Option.elim_some]
        rw [ih _ _ false _ _ (fun h => hne (congrArg some h)),
          ih _ _ true _ _ (fun h => hne (congrArg some h))]
        ring
    · rw [forestLaw_root_forced_expectation]
      cases u <;> cases v
      · exact False.elim (hne rfl)
      · simp [innovation, boolOccupation]
      · simp [innovation, boolOccupation]
      · simp only [innovation, Option.elim_none, Option.elim_some]
        exact ih _ _ false _ _ (fun h => hne (congrArg some h))

end HardCoreActivityThreshold
