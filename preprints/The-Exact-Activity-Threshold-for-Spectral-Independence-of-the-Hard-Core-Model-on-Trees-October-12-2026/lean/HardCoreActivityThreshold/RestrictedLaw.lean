import HardCoreActivityThreshold.WeightedForest

/-! Exact hard-core laws restricted to induced vertex sets, extended by vacant coordinates. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def withinWeight (G : SimpleGraph V) (activity : V → ℝ) (allowed s : Finset V) : ℝ :=
  if s ⊆ allowed then configurationWeight G activity s else 0

theorem withinWeight_sum (G : SimpleGraph V) (activity : V → ℝ) (allowed : Finset V) :
    ∑ s : Finset V, withinWeight G activity allowed s = partitionWithin G activity allowed := by
  unfold partitionWithin
  have he : Forest.independentSetsWithin G allowed =
      univ.filter (fun s => s ⊆ allowed ∧ Independent G s) := by
    ext s
    simp only [Forest.mem_independentSetsWithin, mem_filter, mem_univ, true_and]
    rfl
  rw [he, sum_filter]
  apply sum_congr rfl
  intro s _
  by_cases hs : s ⊆ allowed <;> by_cases hi : Independent G s <;>
    simp [withinWeight, configurationWeight, hs, hi]

noncomputable def hardCoreWithin (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V) : FiniteLaw (Finset V) where
  mass s := withinWeight G activity allowed s / partitionWithin G activity allowed
  nonneg s := by
    apply div_nonneg _ (partitionWithin_pos G activity ha allowed).le
    unfold withinWeight
    split_ifs
    · exact configurationWeight_nonneg G activity (fun v => (ha v).le) s
    · rfl
  sum_one := by
    rw [← sum_div, withinWeight_sum]
    exact div_self (partitionWithin_pos G activity ha allowed).ne'

theorem hardCoreWithin_univ (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) : hardCoreWithin G activity ha univ = hardCoreLaw G activity ha := by
  apply FiniteLaw.ext
  intro s
  simp only [hardCoreWithin, withinWeight, subset_univ, ite_true, partitionWithin_univ,
    hardCoreLaw_mass]

/-- Conditioning all forbidden vertices vacant produces exactly the restricted hard-core law. -/
theorem hardCore_condition_allowed (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (allowed : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (fun s => s ⊆ allowed)) :
    (hardCoreLaw G activity ha).condition (fun s => s ⊆ allowed) hp =
      hardCoreWithin G activity ha allowed := by
  have he : (hardCoreLaw G activity ha).eventMass (fun s => s ⊆ allowed) =
      partitionWithin G activity allowed / partitionFunction G activity := by
    unfold FiniteLaw.eventMass
    rw [← withinWeight_sum]
    rw [sum_div]
    apply sum_congr rfl
    intro s _
    by_cases hs : s ⊆ allowed <;> simp [hs, withinWeight, hardCoreLaw_mass]
  apply FiniteLaw.ext
  intro s
  rw [FiniteLaw.condition_mass, he]
  simp only [hardCoreLaw_mass, hardCoreWithin]
  have hz := (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  by_cases hs : s ⊆ allowed
  · simp only [hs, ite_true, withinWeight]
    field_simp
  · simp [hs, withinWeight]

end HardCoreActivityThreshold
