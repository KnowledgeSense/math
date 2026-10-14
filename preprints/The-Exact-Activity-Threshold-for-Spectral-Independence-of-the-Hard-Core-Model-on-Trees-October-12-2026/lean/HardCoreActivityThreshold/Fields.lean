import HardCoreActivityThreshold.Correlation

/-! External fields and conditional probabilities agree with their finite-law definitions. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem field_expectation_hardCore (G : SimpleGraph V) (activity field : V → ℝ)
    (ha : ∀ v, 0 < activity v) :
    (hardCoreLaw G activity ha).expectation (fieldWeight field) =
      partitionFunction G (fun v => activity v * field v) / partitionFunction G activity := by
  unfold FiniteLaw.expectation partitionFunction
  rw [sum_div]
  apply sum_congr rfl
  intro s _
  rw [hardCoreLaw_mass, configurationWeight_field]
  unfold fieldWeight partitionFunction
  ring

omit [DecidableEq V] in
/-- A local field is exactly a decrease of vertex activities when its coordinates are at most one. -/
theorem applyField_hardCore (G : SimpleGraph V) (activity field : V → ℝ)
    (ha : ∀ v, 0 < activity v) (hf : ∀ v, 0 < field v) :
    applyField (hardCoreLaw G activity ha) field hf =
      hardCoreLaw G (fun v => activity v * field v) (fun v => mul_pos (ha v) (hf v)) := by
  apply FiniteLaw.ext
  intro s
  change ((hardCoreLaw G activity ha).mass s * fieldWeight field s) /
    (hardCoreLaw G activity ha).expectation (fieldWeight field) = _
  rw [field_expectation_hardCore, hardCoreLaw_mass, hardCoreLaw_mass, configurationWeight_field]
  have hz : partitionFunction G activity ≠ 0 :=
    (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  unfold fieldWeight
  field_simp

/-- The occupied conditional probability is the event probability under actual conditioning. -/
theorem conditionalOccupation_true_eq (μ : FiniteLaw (Finset V)) (u v : V)
    (hu : 0 < μ.eventMass (fun s => u ∈ s)) :
    conditionalOccupation μ u true v =
      (μ.condition (fun s => u ∈ s) hu).eventMass (fun s => v ∈ s) := by
  rw [μ.condition_eventMass]
  simp only [conditionalOccupation, ite_true, jointOccupation, marginal_eq_eventMass]

/-- The unoccupied conditional probability is also the actual conditional event probability. -/
theorem conditionalOccupation_false_eq (μ : FiniteLaw (Finset V)) (u v : V)
    (hu : 0 < μ.eventMass (fun s => u ∉ s)) :
    conditionalOccupation μ u false v =
      (μ.condition (fun s => u ∉ s) hu).eventMass (fun s => v ∈ s) := by
  rw [μ.condition_eventMass]
  simp [conditionalOccupation]

omit [Fintype V] [DecidableEq V] in
theorem field_preserves_activity_cap (activity field : V → ℝ) (Λ : ℝ)
    (ha : ∀ v, 0 < activity v) (hcap : ∀ v, activity v ≤ Λ)
    (hf : ∀ v, 0 < field v) (hle : ∀ v, field v ≤ 1) :
    ∀ v, 0 < activity v * field v ∧ activity v * field v ≤ Λ := by
  intro v
  refine ⟨mul_pos (ha v) (hf v), ?_⟩
  exact (mul_le_of_le_one_right (ha v).le (hle v)).trans (hcap v)

end HardCoreActivityThreshold
