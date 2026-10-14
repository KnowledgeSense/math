import HardCoreActivityThreshold.ForestVarianceTensorization
import HardCoreActivityThreshold.CoordinateFlip

/-! Feasible hard-core pinnings are exact coordinate flips of restricted forest laws. -/
namespace HardCoreActivityThreshold
open Finset
open scoped symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pinnedHardCoreLaw_support (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied))
    (s : Finset V) :
    0 < (pinnedHardCoreLaw G activity ha pinned occupied hp).mass s ↔
      Independent G s ∧ agreesWith pinned occupied s := by
  unfold pinnedHardCoreLaw
  rw [FiniteLaw.condition_mass, div_pos_iff_of_pos_right hp]
  by_cases hs : agreesWith pinned occupied s
  · simp only [hs, ite_true, and_true]
    exact hardCoreLaw_support G activity ha s
  · simp [hs]

theorem feasible_pinning_data (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    occupied ⊆ pinned ∧ Independent G occupied := by
  let μ := pinnedHardCoreLaw G activity ha pinned occupied hp
  have he : ∃ s, 0 < μ.mass s := by
    by_contra! h
    have hh : (∑ s, μ.mass s) ≤ 0 := sum_nonpos (fun s _ => h s)
    rw [μ.sum_one] at hh
    norm_num at hh
  obtain ⟨s, hs⟩ := he
  obtain ⟨hi, hagree⟩ := (pinnedHardCoreLaw_support G activity ha pinned occupied hp s).mp hs
  exact ⟨occupied_subset_of_agrees hagree, independent_occupied_of_agrees G hi hagree⟩

theorem freePartition_eq_partitionWithin (G : SimpleGraph V) (activity : V → ℝ)
    (pinned occupied : Finset V) :
    freePartition G activity pinned occupied =
      partitionWithin G activity (freeVertices G pinned occupied) := by
  unfold freePartition
  rw [← withinWeight_sum]
  have he : (∑ s : FreeConfiguration G pinned occupied, configurationWeight G activity s.val) =
      ∑ s : Finset V, if Independent G s ∧ s ⊆ freeVertices G pinned occupied then
        configurationWeight G activity s else 0 := by
    rw [← sum_filter]
    exact (sum_subtype (univ.filter (fun s => Independent G s ∧ s ⊆ freeVertices G pinned occupied))
      (by intro s; simp) (configurationWeight G activity)).symm
  rw [he]
  apply sum_congr rfl
  intro s _
  by_cases hi : Independent G s <;> by_cases hs : s ⊆ freeVertices G pinned occupied <;>
    simp [withinWeight, configurationWeight, hi, hs]

theorem configurationFlip_join_free (G : SimpleGraph V) (pinned occupied : Finset V)
    (hop : occupied ⊆ pinned) (s : Finset V) (hs : s ⊆ freeVertices G pinned occupied) :
    configurationFlip occupied (occupied ∪ s) = s := by
  have hd : Disjoint s occupied := (free_disjoint_occupied G pinned occupied hop hs).symm
  change (occupied ∪ s) ∆ occupied = s
  rw [union_comm, ← Finset.symmDiff_eq_union hd, symmDiff_symmDiff_cancel_right]

theorem join_configurationFlip_free (G : SimpleGraph V) (pinned occupied : Finset V)
    (hop : occupied ⊆ pinned) (s : Finset V)
    (hs : configurationFlip occupied s ⊆ freeVertices G pinned occupied) :
    occupied ∪ configurationFlip occupied s = s := by
  apply (configurationFlip occupied).injective
  exact configurationFlip_join_free G pinned occupied hop _ hs

/-- The equality is on all ambient configurations, including the zero-mass configurations. -/
theorem pinnedHardCoreLaw_eq_flip_within (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    pinnedHardCoreLaw G activity ha pinned occupied hp =
      (hardCoreWithin G activity ha (freeVertices G pinned occupied)).mapEquiv
        (configurationFlip occupied) := by
  obtain ⟨hop, ho⟩ := feasible_pinning_data G activity ha pinned occupied hp
  apply FiniteLaw.ext
  intro s
  by_cases hs : Independent G s ∧ agreesWith pinned occupied s
  · let r : FreeConfiguration G pinned occupied :=
      ⟨s \ pinned, independent_mono G hs.1 sdiff_subset, residual_subset_free G hs.1 hs.2⟩
    have hsplit : occupied ∪ r.val = s := configuration_split hs.2
    rw [← hsplit, pinnedHardCore_probability G activity ha pinned occupied hop ho hp r]
    change _ = (hardCoreWithin G activity ha (freeVertices G pinned occupied)).mass
      (configurationFlip occupied (occupied ∪ r.val))
    rw [configurationFlip_join_free G pinned occupied hop r.val r.property.2]
    simp only [hardCoreWithin, withinWeight, r.property.2, ite_true,
      freePartition_eq_partitionWithin]
  · have hleft : (pinnedHardCoreLaw G activity ha pinned occupied hp).mass s = 0 := by
      apply le_antisymm
      · exact le_of_not_gt (fun h => hs ((pinnedHardCoreLaw_support G activity ha pinned occupied hp s).mp h))
      · exact (pinnedHardCoreLaw G activity ha pinned occupied hp).nonneg s
    rw [hleft]
    change 0 = (hardCoreWithin G activity ha (freeVertices G pinned occupied)).mass
      (configurationFlip occupied s)
    symm
    apply le_antisymm
    · apply le_of_not_gt
      intro h
      obtain ⟨hf, hi⟩ := (hardCoreWithin_support G activity ha
        (freeVertices G pinned occupied) (configurationFlip occupied s)).mp h
      have hsplit := join_configurationFlip_free G pinned occupied hop s hf
      apply hs
      rw [← hsplit]
      exact ⟨independent_join_free G ho hi hf, join_free_agrees G hop hf⟩
    · exact (hardCoreWithin G activity ha (freeVertices G pinned occupied)).nonneg _

/-- Uniform low-activity tensorization after every feasible occupied/vacant pinning. -/
theorem pinned_forest_variance_tensorization (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2)
    (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    VarianceTensorization (pinnedHardCoreLaw G activity ha pinned occupied hp) 18 := by
  rw [pinnedHardCoreLaw_eq_flip_within]
  exact (forest_variance_tensorization G hG activity ha hsmall
    (freeVertices G pinned occupied)).flip occupied

/-- Pinnings retain the same ambient-coordinate low-activity gap bound. -/
theorem pinned_forest_heatBathGap_lower [Nonempty V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2)
    (pinned occupied : Finset V)
    (hp : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied)) :
    1 / (18 * (Fintype.card V : ℝ)) ≤
      heatBathGap (pinnedHardCoreLaw G activity ha pinned occupied hp) :=
  (pinned_forest_variance_tensorization G hG activity ha hsmall pinned occupied hp).heatBathGap_lower
    (by norm_num)

end HardCoreActivityThreshold
