import HardCoreActivityThreshold.ForestParent
import HardCoreActivityThreshold.TreeRootCorrelation

/-! Actual occupation and innovation variances are uniformly comparable to subtree messages. -/
namespace HardCoreActivityThreshold
open Finset Forest
attribute [local instance] Classical.propDecidable

section GeneralGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem partitionWithin_mono (G : SimpleGraph V) (activity : V → ℝ) (ha : ∀ v, 0 < activity v)
    {s t : Finset V} (hst : s ⊆ t) : partitionWithin G activity s ≤ partitionWithin G activity t := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro I hI
    rcases (Forest.mem_independentSetsWithin G).mp hI with ⟨his, hi⟩
    exact (Forest.mem_independentSetsWithin G).mpr ⟨his.trans hst, hi⟩
  · intro I _ _
    exact prod_nonneg (fun v _ => (ha v).le)

theorem hardCore_odds_le_activity (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (v : V) :
    marginal (hardCoreLaw G activity ha) v / (1-marginal (hardCoreLaw G activity ha) v) ≤ activity v := by
  rw [hardCore_occupation_odds]
  apply (div_le_iff₀ (partitionWithin_pos G activity ha _)).mpr
  apply mul_le_mul_of_nonneg_left _ (ha v).le
  apply partitionWithin_mono G activity ha
  intro w hw
  have hh := (Forest.mem_compatibleVertices G).mp hw
  exact mem_erase.mpr ⟨hh.1, hh.2.1⟩

theorem hardCore_marginal_cap (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : V) :
    marginal (hardCoreLaw G activity ha) v ≤ Λ/(1+Λ) := by
  have hm := hardCore_marginal_lt_one G activity ha v
  have ho := (hardCore_odds_le_activity G activity ha v).trans (hcap v)
  have he := (div_le_iff₀ (by linarith : 0 < 1-marginal (hardCoreLaw G activity ha) v)).mp ho
  apply (le_div_iff₀ (by positivity : 0 < 1+Λ)).mpr
  nlinarith

end GeneralGraph

theorem forest_parent_marginal (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    forestMarginal A activity ha false v = vertexMessage A activity v *
      (1 - (forestParent A v).elim 0 (fun w => forestMarginal A activity ha false w)) := by
  have he := innovation_mean A activity ha false v
  change (forestLaw A activity ha false).expectation (fun x => innovation A activity false v x) = 0 at he
  simp_rw [innovation_identity] at he
  rw [FiniteLaw.expectation_add, FiniteLaw.expectation_sub, FiniteLaw.expectation_const,
    FiniteLaw.expectation_smul] at he
  have hp : (forestLaw A activity ha false).expectation (parentOccupation A false v) =
      (forestParent A v).elim 0 (fun w => forestMarginal A activity ha false w) := by
    unfold parentOccupation
    cases forestParent A v
    · simp [boolValue]
    · rfl
  rw [hp] at he
  change forestMarginal A activity ha false v - vertexMessage A activity v + _ = 0 at he
  linarith

theorem forest_marginal_message_bounds (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    vertexMessage A activity v / (1+Λ) ≤ marginal (hardCoreLaw A.graph activity ha) v ∧
      marginal (hardCoreLaw A.graph activity ha) v ≤ vertexMessage A activity v := by
  have hq := (vertexMessage_mem_Ioo A activity ha v).1
  have hp : 0 ≤ (forestParent A v).elim 0 (fun w => forestMarginal A activity ha false w) ∧
      (forestParent A v).elim 0 (fun w => forestMarginal A activity ha false w) ≤ Λ/(1+Λ) := by
    cases he : forestParent A v
    · simp; positivity
    · simp only [Option.elim_some, forestMarginal_free_actual]
      exact ⟨marginal_nonneg _ _, hardCore_marginal_cap _ _ ha hΛ hcap _⟩
  rw [← forestMarginal_free_actual, forest_parent_marginal]
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 1+Λ)).mpr
    have he := (le_div_iff₀ (by positivity : 0 < 1+Λ)).mp hp.2
    have hh := mul_le_mul_of_nonneg_left he hq.le
    nlinarith
  · nlinarith [mul_nonneg hq.le hp.1]

theorem forest_variance_message_lower (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    vertexMessage A activity v / (1+Λ)^2 ≤ occupationVariance (hardCoreLaw A.graph activity ha) v := by
  have hbounds := forest_marginal_message_bounds A activity ha hΛ hcap v
  have hcap' := hardCore_marginal_cap A.graph activity ha hΛ hcap v
  have hvac : 1/(1+Λ) ≤ 1-marginal (hardCoreLaw A.graph activity ha) v := by
    apply (div_le_iff₀ (by positivity : 0 < 1+Λ)).mpr
    have hc := (le_div_iff₀ (by positivity : 0 < 1+Λ)).mp hcap'
    nlinarith
  have hm := mul_le_mul hbounds.1 hvac (by positivity : 0 ≤ 1/(1+Λ)) (marginal_nonneg _ _)
  unfold occupationVariance
  rw [occupation_variance]
  convert hm using 1
  field_simp

/-- The innovation variance is no larger than the subtree occupation message. -/
theorem innovation_second_moment_le (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (parent : Bool) (v : A.Vertex) :
    (forestLaw A activity ha parent).expectation (fun x => (innovation A activity parent v x)^2) ≤
      vertexMessage A activity v := by
  induction A generalizing parent with
  | empty => exact v.elim
  | union A B ihA ihB =>
    cases v with
    | inl v =>
      change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => (fun y => (innovation A (fun v => activity (.inl v)) parent v y)^2) (fun v => x (.inl v))) ≤ _
      rw [forestLaw_union_expectation_left A B activity ha parent
        (fun y => (innovation A (fun v => activity (.inl v)) parent v y)^2)]
      exact ihA _ _ _ _
    | inr v =>
      change (forestLaw (A.union B) activity ha parent).expectation
        (fun x => (fun y => (innovation B (fun v => activity (.inr v)) parent v y)^2) (fun v => x (.inr v))) ≤ _
      rw [forestLaw_union_expectation_right A B activity ha parent
        (fun y => (innovation B (fun v => activity (.inr v)) parent v y)^2)]
      exact ihB _ _ _ _
  | root A ih =>
    have hq : 0 < downwardOccupation A activity ∧ downwardOccupation A activity < 1 :=
      ⟨downwardOccupation_pos A activity ha, downwardOccupation_lt_one A activity ha⟩
    cases parent
    · rw [forestLaw_root_free_expectation]
      cases v with
      | none =>
        simp only [innovation, vertexMessage, boolOccupation, Option.elim_none,
          Bool.false_eq_true, ↓reduceIte, FiniteLaw.expectation_const]
        nlinarith [sq_nonneg (downwardOccupation A activity)]
      | some v =>
        simp only [innovation, vertexMessage, Option.elim_none, Option.elim_some]
        have h0 := ih (fun v => activity (some v)) (fun v => ha (some v)) false v
        have h1 := ih (fun v => activity (some v)) (fun v => ha (some v)) true v
        have hb0 := mul_le_mul_of_nonneg_left h0 (by linarith [hq.2] : 0 ≤ 1-downwardOccupation A activity)
        have hb1 := mul_le_mul_of_nonneg_left h1 hq.1.le
        nlinarith
    · rw [forestLaw_root_forced_expectation]
      cases v with
      | none => simpa [innovation, boolOccupation, vertexMessage] using hq.1.le
      | some v =>
        simp only [innovation, vertexMessage, Option.elim_none, Option.elim_some]
        exact ih _ _ false v

end HardCoreActivityThreshold
