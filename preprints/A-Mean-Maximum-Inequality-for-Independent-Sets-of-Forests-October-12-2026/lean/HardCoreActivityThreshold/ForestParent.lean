import HardCoreActivityThreshold.ForestInnovations

/-! Parent maps and innovation identities for the actual rooted forest graphs. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

def forestParent : (A : ForestExpr) → A.Vertex → Option A.Vertex
  | .empty, v => v.elim
  | .union A _, .inl v => (forestParent A v).map Sum.inl
  | .union _ B, .inr v => (forestParent B v).map Sum.inr
  | .root _, none => none
  | .root A, some v => some (forestParent A v)

theorem forestParent_eq_none (A : ForestExpr) (v : A.Vertex) :
    forestParent A v = none ↔ A.IsRoot v := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB => cases v <;> simp only [forestParent, Option.map_eq_none_iff, ForestExpr.IsRoot] <;>
      first | exact ihA _ | exact ihB _
  | root A ih => cases v <;> simp [forestParent, ForestExpr.IsRoot]

theorem forestParent_depth (A : ForestExpr) (u v : A.Vertex) (hp : forestParent A u = some v) :
    A.depth u = A.depth v + 1 := by
  induction A with
  | empty => exact u.elim
  | union A B ihA ihB =>
    cases u <;> cases v <;> simp only [forestParent, Option.map_eq_some_iff] at hp
    · obtain ⟨w, hw, he⟩ := hp
      cases he
      exact ihA _ _ hw
    · obtain ⟨w, _, he⟩ := hp; cases he
    · obtain ⟨w, _, he⟩ := hp; cases he
    · obtain ⟨w, hw, he⟩ := hp
      cases he
      exact ihB _ _ hw
  | root A ih =>
    cases u with
    | none => cases hp
    | some u =>
      simp only [forestParent, Option.some.injEq] at hp
      cases v with
      | none =>
        have hz := (A.isRoot_iff_depth_zero u).mp ((forestParent_eq_none A u).mp hp)
        simp [ForestExpr.depth, hz]
      | some v =>
        have he := ih u v hp
        simp only [ForestExpr.depth]
        omega

theorem forestParent_adj (A : ForestExpr) (u v : A.Vertex) (hp : forestParent A u = some v) :
    A.graph.Adj u v := by
  induction A with
  | empty => exact u.elim
  | union A B ihA ihB =>
    cases u <;> cases v <;> simp only [forestParent, Option.map_eq_some_iff] at hp
    · obtain ⟨w, hw, he⟩ := hp; cases he; exact ihA _ _ hw
    · obtain ⟨w, _, he⟩ := hp; cases he
    · obtain ⟨w, _, he⟩ := hp; cases he
    · obtain ⟨w, hw, he⟩ := hp; cases he; exact ihB _ _ hw
  | root A ih =>
    cases u with
    | none => cases hp
    | some u =>
      simp only [forestParent, Option.some.injEq] at hp
      cases v with
      | none => exact (forestParent_eq_none A u).mp hp
      | some v => exact ih u v hp

noncomputable def boolValue (b : Bool) : ℝ := if b then 1 else 0

noncomputable def parentOccupation (A : ForestExpr) (parent : Bool) (v : A.Vertex)
    (x : A.Vertex → Bool) : ℝ :=
  (forestParent A v).elim (boolValue parent) (fun w => boolOccupation w x)

/-- The innovation is the actual occupation minus its exact parent-dependent mean. -/
theorem innovation_identity (A : ForestExpr) (activity : A.Vertex → ℝ) (parent : Bool)
    (v : A.Vertex) (x : A.Vertex → Bool) :
    innovation A activity parent v x = boolOccupation v x - vertexMessage A activity v +
      vertexMessage A activity v * parentOccupation A parent v x := by
  induction A generalizing parent with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v =>
      rw [innovation, ihA]
      simp only [vertexMessage, parentOccupation, forestParent]
      cases forestParent A v <;> rfl
    | inr v =>
      rw [innovation, ihB]
      simp only [vertexMessage, parentOccupation, forestParent]
      cases forestParent B v <;> rfl
  | root A ih =>
    cases v with
    | none => cases parent <;> simp [innovation, vertexMessage, parentOccupation, forestParent, boolValue]
    | some v =>
      rw [innovation, ih]
      simp only [vertexMessage, parentOccupation, forestParent, Option.elim_some]
      cases forestParent A v <;> rfl

theorem vertexMessage_mem_Ioo (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    0 < vertexMessage A activity v ∧ vertexMessage A activity v < 1 := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => exact ihA (fun v => activity (.inl v)) (fun v => ha (.inl v)) v
    | inr v => exact ihB (fun v => activity (.inr v)) (fun v => ha (.inr v)) v
  | root A ih =>
    cases v
    · exact ⟨downwardOccupation_pos A activity ha, downwardOccupation_lt_one A activity ha⟩
    · exact ih (fun v => activity (some v)) (fun v => ha (some v)) _

end HardCoreActivityThreshold
