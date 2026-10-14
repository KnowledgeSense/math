import HardCoreActivityThreshold.ForestMarginalBounds
import HardCoreActivityThreshold.StationaryActivities

/-! Exact positive subtree odds and logarithmic recursions on actual finite forests. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

noncomputable def vertexOdds : (A : ForestExpr) → (A.Vertex → ℝ) → A.Vertex → ℝ
  | .empty, _, v => v.elim
  | .union A _, activity, .inl v => vertexOdds A (fun v => activity (.inl v)) v
  | .union _ B, activity, .inr v => vertexOdds B (fun v => activity (.inr v)) v
  | .root A, activity, none => activity none * weightedAvoidRoots A (fun v => activity (some v)) /
      weightedTotal A (fun v => activity (some v))
  | .root A, activity, some v => vertexOdds A (fun v => activity (some v)) v

noncomputable def rootLogSum : (A : ForestExpr) → (A.Vertex → ℝ) → ℝ
  | .empty, _ => 0
  | .union A B, activity => rootLogSum A (fun v => activity (.inl v)) + rootLogSum B (fun v => activity (.inr v))
  | .root A, activity => Real.log (1+vertexOdds A.root activity none)

noncomputable def vertexLogPotential : (A : ForestExpr) → (A.Vertex → ℝ) → A.Vertex → ℝ
  | .empty, _, v => v.elim
  | .union A _, activity, .inl v => vertexLogPotential A (fun v => activity (.inl v)) v
  | .union _ B, activity, .inr v => vertexLogPotential B (fun v => activity (.inr v)) v
  | .root A, activity, none => rootLogSum A (fun v => activity (some v))
  | .root A, activity, some v => vertexLogPotential A (fun v => activity (some v)) v

theorem vertexOdds_pos (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (v : A.Vertex) : 0 < vertexOdds A activity v := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => exact ihA _ (fun v => ha (.inl v)) v
    | inr v => exact ihB _ (fun v => ha (.inr v)) v
  | root A ih =>
    cases v with
    | none =>
      exact div_pos (mul_pos (ha none) (partitionWithin_pos _ _ (fun v => ha (some v)) _))
        (partitionWithin_pos _ _ (fun v => ha (some v)) _)
    | some v => exact ih _ (fun v => ha (some v)) v

theorem vertexMessage_eq_odds (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (v : A.Vertex) : vertexMessage A activity v = vertexOdds A activity v / (1+vertexOdds A activity v) := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => exact ihA _ (fun v => ha (.inl v)) v
    | inr v => exact ihB _ (fun v => ha (.inr v)) v
  | root A ih =>
    cases v with
    | none =>
      rw [vertexMessage, downwardOccupation_ratio A activity ha]
      simp only [vertexOdds, mul_div_assoc]
    | some v => exact ih _ (fun v => ha (some v)) v

theorem rootLogSum_eq_sum (A : ForestExpr) (activity : A.Vertex → ℝ) :
    rootLogSum A activity = ∑ v, if A.IsRoot v then Real.log (1+vertexOdds A activity v) else 0 := by
  induction A with
  | empty => simp [rootLogSum]
  | union A B ihA ihB => rw [Fintype.sum_sum_type, rootLogSum, ihA, ihB]; rfl
  | root A ih =>
    rw [Fintype.sum_option]
    simp [rootLogSum, ForestExpr.IsRoot]

theorem rootLogSum_nonneg (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v) :
    0 ≤ rootLogSum A activity := by
  rw [rootLogSum_eq_sum]
  apply sum_nonneg
  intro v _
  split_ifs
  · exact Real.log_nonneg (by linarith [vertexOdds_pos A activity ha v])
  · rfl

theorem weightedRatio_exp (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v) :
    weightedAvoidRoots A activity / weightedTotal A activity = Real.exp (-rootLogSum A activity) := by
  induction A with
  | empty => simp [rootLogSum]
  | union A B ihA ihB =>
    rw [weightedAvoidRoots_union, weightedTotal_union, mul_div_mul_comm, ihA _ (fun v => ha (.inl v)),
      ihB _ (fun v => ha (.inr v)), rootLogSum, neg_add, Real.exp_add]
  | root A ih =>
    rw [root_avoid_ratio A activity ha]
    change 1-vertexMessage A.root activity none = _
    rw [vertexMessage_eq_odds A.root activity ha none, rootLogSum, Real.exp_neg,
      Real.exp_log (by linarith [vertexOdds_pos A.root activity ha none])]
    have hd : 1+vertexOdds A.root activity none ≠ 0 := by
      have := vertexOdds_pos A.root activity ha none
      positivity
    field_simp
    ring

theorem vertexOdds_exp (A : ForestExpr) (activity : A.Vertex → ℝ) (ha : ∀ v, 0 < activity v)
    (v : A.Vertex) : vertexOdds A activity v = activity v * Real.exp (-vertexLogPotential A activity v) := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => exact ihA _ (fun v => ha (.inl v)) v
    | inr v => exact ihB _ (fun v => ha (.inr v)) v
  | root A ih =>
    cases v with
    | none => rw [vertexOdds, mul_div_assoc, weightedRatio_exp A _ (fun v => ha (some v))]; rfl
    | some v => exact ih _ (fun v => ha (some v)) v

theorem vertexLogPotential_nonneg (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : 0 ≤ vertexLogPotential A activity v := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => exact ihA _ (fun v => ha (.inl v)) v
    | inr v => exact ihB _ (fun v => ha (.inr v)) v
  | root A ih =>
    cases v with
    | none => exact rootLogSum_nonneg A _ (fun v => ha (some v))
    | some v => exact ih _ (fun v => ha (some v)) v

theorem vertexOdds_le_activity (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : vertexOdds A activity v ≤ activity v := by
  rw [vertexOdds_exp A activity ha v]
  exact mul_le_of_le_one_right (ha v).le (Real.exp_le_one_iff.mpr (by linarith [vertexLogPotential_nonneg A activity ha v]))

theorem vertexLogPotential_eq_log (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    vertexLogPotential A activity v = Real.log (activity v / vertexOdds A activity v) := by
  rw [vertexOdds_exp A activity ha v]
  have he : activity v / (activity v * Real.exp (-vertexLogPotential A activity v)) =
      Real.exp (vertexLogPotential A activity v) := by
    rw [Real.exp_neg]
    field_simp [(ha v).ne']
  rw [he, Real.log_exp]

noncomputable def childSum (A : ForestExpr) (f : A.Vertex → ℝ) (v : A.Vertex) : ℝ :=
  ∑ u, if forestParent A u = some v then f u else 0

theorem childSum_union_left (A B : ForestExpr) (f : (A.union B).Vertex → ℝ) (v : A.Vertex) :
    childSum (A.union B) f (.inl v) = childSum A (fun u => f (.inl u)) v := by
  unfold childSum
  rw [Fintype.sum_sum_type]
  simp [forestParent, Option.map_eq_some_iff]

theorem childSum_union_right (A B : ForestExpr) (f : (A.union B).Vertex → ℝ) (v : B.Vertex) :
    childSum (A.union B) f (.inr v) = childSum B (fun u => f (.inr u)) v := by
  unfold childSum
  rw [Fintype.sum_sum_type]
  simp [forestParent, Option.map_eq_some_iff]

theorem childSum_root (A : ForestExpr) (f : A.root.Vertex → ℝ) :
    childSum A.root f none = ∑ u, if A.IsRoot u then f (some u) else 0 := by
  unfold childSum
  rw [Fintype.sum_option]
  simp [forestParent, forestParent_eq_none]

theorem childSum_child (A : ForestExpr) (f : A.root.Vertex → ℝ) (v : A.Vertex) :
    childSum A.root f (some v) = childSum A (fun u => f (some u)) v := by
  unfold childSum
  rw [Fintype.sum_option]
  simp [forestParent]

/-- The local logarithmic potential is the sum of the actual child log-odds. -/
theorem vertexLogPotential_children (A : ForestExpr) (activity : A.Vertex → ℝ) (v : A.Vertex) :
    vertexLogPotential A activity v = childSum A (fun u => Real.log (1+vertexOdds A activity u)) v := by
  induction A with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v => rw [childSum_union_left]; exact ihA _ v
    | inr v => rw [childSum_union_right]; exact ihB _ v
  | root A ih =>
    cases v with
    | none => rw [childSum_root]; exact rootLogSum_eq_sum A _
    | some v => rw [childSum_child]; exact ih _ v

theorem vertexLogPotential_cap (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    vertexLogPotential A activity v ≤ Real.log (Λ/vertexOdds A activity v) := by
  rw [vertexLogPotential_eq_log A activity ha v]
  exact Real.strictMonoOn_log.monotoneOn
    (div_pos (ha v) (vertexOdds_pos A activity ha v))
    (div_pos hΛ (vertexOdds_pos A activity ha v))
    (div_le_div_of_nonneg_right (hcap v) (vertexOdds_pos A activity ha v).le)

theorem vertexMessage_le_log (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    vertexMessage A activity v ≤ Real.log (1+vertexOdds A activity v) := by
  rw [vertexMessage_eq_odds A activity ha v]
  have ho := vertexOdds_pos A activity ha v
  have he : vertexOdds A activity v / (1+vertexOdds A activity v) = 1-(1+vertexOdds A activity v)⁻¹ := by
    have hn : 1+vertexOdds A activity v ≠ 0 := by positivity
    field_simp
    ring
  rw [he]
  exact Real.one_sub_inv_le_log_of_pos (by positivity)

theorem childSum_messages_le_logPotential (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    childSum A (vertexMessage A activity) v ≤ vertexLogPotential A activity v := by
  rw [vertexLogPotential_children]
  apply sum_le_sum
  intro u _
  split_ifs
  · exact vertexMessage_le_log A activity ha u
  · rfl

end HardCoreActivityThreshold
