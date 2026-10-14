import HardCoreActivityThreshold.Fields
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The combinatorial reduction of feasible pinnings to an induced forest. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unpinned vertices that are not forced vacant by an occupied pinned neighbor. -/
noncomputable def freeVertices (G : SimpleGraph V) (pinned occupied : Finset V) : Finset V :=
  univ.filter (fun v => v ∉ pinned ∧ ∀ w ∈ occupied, ¬ G.Adj v w)

@[simp] theorem mem_freeVertices (G : SimpleGraph V) (pinned occupied : Finset V) (v : V) :
    v ∈ freeVertices G pinned occupied ↔ v ∉ pinned ∧ ∀ w ∈ occupied, ¬ G.Adj v w := by
  simp [freeVertices]

omit [Fintype V] [DecidableEq V] in
theorem independent_mono (G : SimpleGraph V) {s t : Finset V}
    (hs : Independent G s) (ht : t ⊆ s) : Independent G t :=
  fun u hu v hv => hs u (ht hu) v (ht hv)

omit [Fintype V] in
theorem occupied_subset_of_agrees {pinned occupied s : Finset V}
    (h : agreesWith pinned occupied s) : occupied ⊆ pinned := by
  unfold agreesWith at h
  rw [← h]
  exact inter_subset_right

omit [Fintype V] in
theorem occupied_subset_configuration {pinned occupied s : Finset V}
    (h : agreesWith pinned occupied s) : occupied ⊆ s := by
  unfold agreesWith at h
  rw [← h]
  exact inter_subset_left

omit [Fintype V] in
theorem independent_occupied_of_agrees (G : SimpleGraph V) {pinned occupied s : Finset V}
    (hi : Independent G s) (h : agreesWith pinned occupied s) : Independent G occupied :=
  independent_mono G hi (occupied_subset_configuration h)

theorem residual_subset_free (G : SimpleGraph V) {pinned occupied s : Finset V}
    (hi : Independent G s) (h : agreesWith pinned occupied s) :
    s \ pinned ⊆ freeVertices G pinned occupied := by
  intro v hv
  rcases mem_sdiff.mp hv with ⟨hvs, hvp⟩
  rw [mem_freeVertices]
  refine ⟨hvp, ?_⟩
  intro w hw
  exact hi v hvs w (occupied_subset_configuration h hw)

omit [Fintype V] in
theorem configuration_split {pinned occupied s : Finset V}
    (h : agreesWith pinned occupied s) : occupied ∪ (s \ pinned) = s := by
  unfold agreesWith at h
  rw [← h]
  ext v
  simp only [mem_union, mem_inter, mem_sdiff]
  tauto

theorem free_disjoint_pinned (G : SimpleGraph V) (pinned occupied : Finset V)
    {s : Finset V} (hs : s ⊆ freeVertices G pinned occupied) : Disjoint s pinned := by
  rw [disjoint_left]
  intro v hv hp
  exact ((mem_freeVertices G pinned occupied v).mp (hs hv)).1 hp

theorem free_disjoint_occupied (G : SimpleGraph V) (pinned occupied : Finset V)
    (hop : occupied ⊆ pinned) {s : Finset V} (hs : s ⊆ freeVertices G pinned occupied) :
    Disjoint occupied s := by
  rw [disjoint_left]
  intro v ho hv
  exact ((mem_freeVertices G pinned occupied v).mp (hs hv)).1 (hop ho)

theorem independent_join_free (G : SimpleGraph V) {pinned occupied s : Finset V}
    (ho : Independent G occupied) (hs : Independent G s)
    (hfree : s ⊆ freeVertices G pinned occupied) : Independent G (occupied ∪ s) := by
  intro u hu v hv
  rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
  · exact ho u hu v hv
  · exact fun huv => ((mem_freeVertices G pinned occupied v).mp (hfree hv)).2 u hu huv.symm
  · exact ((mem_freeVertices G pinned occupied u).mp (hfree hu)).2 v hv
  · exact hs u hu v hv

theorem join_free_agrees (G : SimpleGraph V) {pinned occupied s : Finset V}
    (hop : occupied ⊆ pinned) (hfree : s ⊆ freeVertices G pinned occupied) :
    agreesWith pinned occupied (occupied ∪ s) := by
  unfold agreesWith
  ext v
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨ho | hs, hp⟩
    · exact ho
    · exact False.elim (((mem_freeVertices G pinned occupied v).mp (hfree hs)).1 hp)
  · intro ho
    exact ⟨Or.inl ho, hop ho⟩

theorem join_free_residual (G : SimpleGraph V) {pinned occupied s : Finset V}
    (hop : occupied ⊆ pinned) (hfree : s ⊆ freeVertices G pinned occupied) :
    (occupied ∪ s) \ pinned = s := by
  ext v
  simp only [mem_sdiff, mem_union]
  constructor
  · rintro ⟨ho | hs, hp⟩
    · exact False.elim (hp (hop ho))
    · exact hs
  · intro hs
    exact ⟨Or.inr hs, ((mem_freeVertices G pinned occupied v).mp (hfree hs)).1⟩

abbrev PinnedConfiguration (G : SimpleGraph V) (pinned occupied : Finset V) :=
  {s : Finset V // Independent G s ∧ agreesWith pinned occupied s}

abbrev FreeConfiguration (G : SimpleGraph V) (pinned occupied : Finset V) :=
  {s : Finset V // Independent G s ∧ s ⊆ freeVertices G pinned occupied}

/-- This bijection removes the pinned occupied set; no feasible configurations are discarded. -/
noncomputable def pinningEquiv (G : SimpleGraph V) (pinned occupied : Finset V)
    (hop : occupied ⊆ pinned) (ho : Independent G occupied) :
    PinnedConfiguration G pinned occupied ≃ FreeConfiguration G pinned occupied where
  toFun s := ⟨s.val \ pinned,
    independent_mono G s.property.1 sdiff_subset,
    residual_subset_free G s.property.1 s.property.2⟩
  invFun s := ⟨occupied ∪ s.val,
    independent_join_free G ho s.property.1 s.property.2,
    join_free_agrees G hop s.property.2⟩
  left_inv s := Subtype.ext (configuration_split s.property.2)
  right_inv s := Subtype.ext (join_free_residual G hop s.property.2)

/-- Exact factorization of the configuration weight under the pinning bijection. -/
theorem pinning_weight_factorization (G : SimpleGraph V) (activity : V → ℝ)
    (pinned occupied : Finset V) (hop : occupied ⊆ pinned) (ho : Independent G occupied)
    (s : FreeConfiguration G pinned occupied) :
    configurationWeight G activity ((pinningEquiv G pinned occupied hop ho).symm s).val =
      (∏ v ∈ occupied, activity v) * configurationWeight G activity s.val := by
  change configurationWeight G activity (occupied ∪ s.val) = _
  simp only [configurationWeight, independent_join_free G ho s.property.1 s.property.2,
    s.property.1, ite_true]
  exact prod_union (free_disjoint_occupied G pinned occupied hop s.property.2)

/-- The remaining graph is a forest whenever the original graph is a forest. -/
theorem free_induced_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic)
    (pinned occupied : Finset V) :
    (G.induce {v | v ∈ freeVertices G pinned occupied}).IsAcyclic := hG.induce _

end HardCoreActivityThreshold

namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable instance pinnedConfigurationFintype (G : SimpleGraph V) (pinned occupied : Finset V) :
    Fintype (PinnedConfiguration G pinned occupied) := inferInstance
noncomputable instance freeConfigurationFintype (G : SimpleGraph V) (pinned occupied : Finset V) :
    Fintype (FreeConfiguration G pinned occupied) := inferInstance

noncomputable def pinnedPartition (G : SimpleGraph V) (activity : V → ℝ)
    (pinned occupied : Finset V) : ℝ :=
  ∑ s : PinnedConfiguration G pinned occupied, configurationWeight G activity s.val

noncomputable def freePartition (G : SimpleGraph V) (activity : V → ℝ)
    (pinned occupied : Finset V) : ℝ :=
  ∑ s : FreeConfiguration G pinned occupied, configurationWeight G activity s.val

theorem hardCore_eventMass_pinning (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (pinned occupied : Finset V) :
    (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied) =
      pinnedPartition G activity pinned occupied / partitionFunction G activity := by
  unfold FiniteLaw.eventMass pinnedPartition
  have hs : (∑ s : PinnedConfiguration G pinned occupied, configurationWeight G activity s.val) =
      ∑ s : Finset V, if Independent G s ∧ agreesWith pinned occupied s then
        configurationWeight G activity s else 0 := by
    rw [← sum_filter]
    exact (sum_subtype (univ.filter (fun s => Independent G s ∧ agreesWith pinned occupied s))
      (by intro s; simp) (configurationWeight G activity)).symm
  rw [hs, sum_div]
  apply sum_congr rfl
  intro s _
  by_cases hi : Independent G s <;> by_cases hp : agreesWith pinned occupied s <;>
    simp [hardCoreLaw_mass, hi, hp, configurationWeight]

theorem pinnedPartition_factor (G : SimpleGraph V) (activity : V → ℝ)
    (pinned occupied : Finset V) (hop : occupied ⊆ pinned) (ho : Independent G occupied) :
    pinnedPartition G activity pinned occupied =
      (∏ v ∈ occupied, activity v) * freePartition G activity pinned occupied := by
  unfold pinnedPartition freePartition
  rw [mul_sum]
  apply Fintype.sum_equiv (pinningEquiv G pinned occupied hop ho)
  intro s
  have h := pinning_weight_factorization G activity pinned occupied hop ho
    ((pinningEquiv G pinned occupied hop ho) s)
  simpa using h

theorem freePartition_pos (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (pinned occupied : Finset V) :
    0 < freePartition G activity pinned occupied := by
  apply sum_pos'
  · intro s _
    exact configurationWeight_nonneg G activity (fun v => (ha v).le) s.val
  · refine ⟨⟨∅, independent_empty G, empty_subset _⟩, mem_univ _, ?_⟩
    simp

/-- Exact pinned probabilities after removing the fixed occupied set. -/
theorem pinnedHardCore_probability (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ v, 0 < activity v) (pinned occupied : Finset V)
    (hop : occupied ⊆ pinned) (ho : Independent G occupied)
    (hfeasible : 0 < (hardCoreLaw G activity ha).eventMass (agreesWith pinned occupied))
    (s : FreeConfiguration G pinned occupied) :
    (pinnedHardCoreLaw G activity ha pinned occupied hfeasible).mass (occupied ∪ s.val) =
      configurationWeight G activity s.val / freePartition G activity pinned occupied := by
  unfold pinnedHardCoreLaw
  rw [FiniteLaw.condition_mass, ite_eq_left (join_free_agrees G hop s.property.2),
    hardCoreLaw_mass, hardCore_eventMass_pinning, pinnedPartition_factor G activity pinned occupied hop ho]
  have hw := pinning_weight_factorization G activity pinned occupied hop ho s
  change configurationWeight G activity (occupied ∪ s.val) = _ at hw
  rw [hw]
  have hprod : (∏ v ∈ occupied, activity v) ≠ 0 :=
    (prod_pos (fun v _ => ha v)).ne'
  have hz : partitionFunction G activity ≠ 0 :=
    (partitionFunction_pos G activity (fun v => (ha v).le)).ne'
  field_simp

end HardCoreActivityThreshold
