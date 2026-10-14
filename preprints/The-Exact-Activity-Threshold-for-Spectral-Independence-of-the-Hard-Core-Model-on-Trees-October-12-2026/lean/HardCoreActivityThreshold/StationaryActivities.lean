import HardCoreActivityThreshold.TreeRootCorrelation

/-! Explicit positive activities realizing a prescribed stationary broadcast on an actual tree. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

def forestRootCount : ForestExpr → ℕ
  | .empty => 0
  | .union A B => forestRootCount A + forestRootCount B
  | .root _ => 1

noncomputable def messageActivities (p : ℝ) : (A : ForestExpr) → A.Vertex → ℝ
  | .empty, v => v.elim
  | .union A _, .inl v => messageActivities p A v
  | .union _ B, .inr v => messageActivities p B v
  | .root A, none => p / (1-p)^(forestRootCount A + 1)
  | .root A, some v => messageActivities p A v

theorem messageActivities_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : ForestExpr) :
    ∀ v, 0 < messageActivities p A v := by
  intro v
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB => cases v <;> first | exact ihA _ | exact ihB _
  | root A ih =>
    cases v
    · exact div_pos hp (pow_pos (by linarith) _)
    · exact ih _

theorem root_avoid_ratio (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    weightedAvoidRoots A.root activity / weightedTotal A.root activity = 1 - downwardOccupation A activity := by
  have hz : weightedTotal A.root activity ≠ 0 := ne_of_gt (partitionWithin_pos _ _ ha _)
  unfold downwardOccupation
  rw [weightedAvoidRoots_root]
  apply (div_eq_iff hz).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hz, weightedTotal_root]
  ring

theorem downwardOccupation_ratio (A : ForestExpr) (activity : A.root.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    downwardOccupation A activity =
      (activity none * (weightedAvoidRoots A (fun v => activity (some v)) /
        weightedTotal A (fun v => activity (some v)))) /
      (1 + activity none * (weightedAvoidRoots A (fun v => activity (some v)) /
        weightedTotal A (fun v => activity (some v)))) := by
  have ht : weightedTotal A (fun v => activity (some v)) ≠ 0 := ne_of_gt (partitionWithin_pos _ _ (fun v => ha (some v)) _)
  have hz : weightedTotal A.root activity ≠ 0 := ne_of_gt (partitionWithin_pos _ _ ha _)
  unfold downwardOccupation
  rw [weightedTotal_root] at hz ⊢
  field_simp

private theorem message_scalar {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : ℕ) :
    (p / (1-p)^(c+1) * (1-p)^c) / (1 + p / (1-p)^(c+1) * (1-p)^c) = p := by
  have h : 1-p ≠ 0 := by linarith
  rw [pow_succ]
  field_simp
  ring

/-- All the messages and the root-vacancy partition ratio are exact, with no limiting model. -/
theorem messageActivities_properties {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : ForestExpr) :
    RegularMessages p A (messageActivities p A) ∧
      weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A) =
        (1-p)^(forestRootCount A) := by
  induction A with
  | empty => simp [RegularMessages, forestRootCount]
  | union A B ihA ihB =>
    refine ⟨⟨ihA.1, ihB.1⟩, ?_⟩
    rw [weightedAvoidRoots_union, weightedTotal_union, mul_div_mul_comm]
    change (weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A)) *
      (weightedAvoidRoots B (messageActivities p B) / weightedTotal B (messageActivities p B)) = _
    rw [ihA.2, ihB.2]
    exact (pow_add _ _ _).symm
  | root A ih =>
    have hq : downwardOccupation A (messageActivities p A.root) = p := by
      rw [downwardOccupation_ratio A _ (messageActivities_pos hp hp1 A.root)]
      change (p / (1-p)^(forestRootCount A+1) *
        (weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A))) /
        (1 + p / (1-p)^(forestRootCount A+1) *
        (weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A))) = p
      rw [ih.2]
      exact message_scalar hp hp1 _
    refine ⟨⟨hq, ih.1⟩, ?_⟩
    rw [root_avoid_ratio A _ (messageActivities_pos hp hp1 A.root), hq]
    simp [forestRootCount]

noncomputable def stationaryActivities (p : ℝ) (A : ForestExpr) : A.root.Vertex → ℝ
  | none => p / (1-p)^(forestRootCount A)
  | some v => messageActivities p A v

theorem stationaryActivities_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : ForestExpr) :
    ∀ v, 0 < stationaryActivities p A v := by
  intro v
  cases v
  · exact div_pos hp (pow_pos (by linarith) _)
  · exact messageActivities_pos hp hp1 A _

theorem stationaryActivities_root {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : ForestExpr) :
    downwardOccupation A (stationaryActivities p A) = stationaryOccupation p := by
  rw [downwardOccupation_ratio A _ (stationaryActivities_pos hp hp1 A)]
  change (p / (1-p)^(forestRootCount A) *
    (weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A))) /
    (1 + p / (1-p)^(forestRootCount A) *
    (weightedAvoidRoots A (messageActivities p A) / weightedTotal A (messageActivities p A))) = _
  rw [(messageActivities_properties hp hp1 A).2, div_mul_cancel₀ _ (pow_ne_zero _ (by linarith))]
  rfl

/-- An explicit finite hard-core tree realizes the exact stationary root correlations. -/
theorem stationaryActivities_correlation {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A : ForestExpr)
    (v : A.root.Vertex) :
    correlationMatrix (hardCoreLaw A.root.graph (stationaryActivities p A)
      (stationaryActivities_pos hp hp1 A)) none v = (-p)^(A.root.depth v) :=
  stationary_core_root_correlation p hp A _ _ (stationaryActivities_root hp hp1 A)
    (messageActivities_properties hp hp1 A).1 v

end HardCoreActivityThreshold
