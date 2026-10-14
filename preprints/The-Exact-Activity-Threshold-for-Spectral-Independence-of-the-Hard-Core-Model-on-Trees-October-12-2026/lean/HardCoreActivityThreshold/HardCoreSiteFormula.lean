import HardCoreActivityThreshold.HardCoreLeafLaw

/-! Explicit local variance and projection formulae for genuine hard-core laws. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hardCoreWithin_support (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed s : Finset V) :
    0 < (hardCoreWithin G activity ha allowed).mass s ↔
      s ⊆ allowed ∧ Independent G s := by
  change 0 < withinWeight G activity allowed s / partitionWithin G activity allowed ↔ _
  rw [div_pos_iff_of_pos_right (partitionWithin_pos G activity ha allowed)]
  by_cases hs : s ⊆ allowed
  · simp only [withinWeight, hs, ite_true, true_and]
    exact configurationWeight_pos_iff G activity ha s
  · simp [withinWeight, hs]

theorem hardCoreWithin_mass_insert (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v : V) (hv : v ∈ allowed)
    (s : Finset V) (hs : v ∉ s) :
    (hardCoreWithin G activity ha allowed).mass (insert v s) =
      if ∀ w ∈ s, ¬ G.Adj v w then
        activity v * (hardCoreWithin G activity ha allowed).mass s else 0 := by
  change withinWeight G activity allowed (insert v s) / _ = _
  rw [withinWeight_insert G activity allowed s v hv hs]
  split_ifs <;> simp only [hardCoreWithin, zero_div]
  ring

theorem hardCoreWithin_mass_zero_of_not_subset (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed s : Finset V) (hs : ¬ s ⊆ allowed) :
    (hardCoreWithin G activity ha allowed).mass s = 0 := by
  simp [hardCoreWithin, withinWeight, hs]

theorem hardCoreWithin_insert_mass_zero (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v : V)
    (hv : v ∉ allowed) (s : Finset V) :
    (hardCoreWithin G activity ha allowed).mass (insert v s) = 0 := by
  apply hardCoreWithin_mass_zero_of_not_subset
  simp only [insert_subset_iff, hv, false_and, not_false_eq_true]

theorem hardCoreWithin_siteVariance (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v : V) (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) v f =
      ∑ s, if v ∉ s then (hardCoreWithin G activity ha allowed).mass (insert v s) /
        (1 + activity v) * (f s - f (insert v s))^2 else 0 := by
  rw [siteConditionalVariance_eq_pairs]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s
  · simp only [hs, not_false_eq_true, ite_true]
    by_cases hv : v ∈ allowed
    · rw [hardCoreWithin_mass_insert G activity ha allowed v hv s hs]
      split_ifs with hn
      · by_cases hz : (hardCoreWithin G activity ha allowed).mass s = 0
        · simp [hz]
        · congr 1
          have hd : 1 + activity v ≠ 0 := by linarith [ha v]
          have he : (hardCoreWithin G activity ha allowed).mass s +
              activity v * (hardCoreWithin G activity ha allowed).mass s =
              (hardCoreWithin G activity ha allowed).mass s * (1 + activity v) := by ring
          rw [he]
          field_simp
      · simp
    · rw [hardCoreWithin_insert_mass_zero G activity ha allowed v hv s]
      simp
  · simp [hs]

theorem hardCoreWithin_siteVariance_forbidden (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v : V)
    (hv : v ∉ allowed) (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) v f = 0 := by
  rw [hardCoreWithin_siteVariance]
  simp [hardCoreWithin_insert_mass_zero G activity ha allowed v hv]

theorem hardCoreWithin_leaf_mass (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u)
    (s : Finset V) (hs : v ∉ s) :
    (hardCoreWithin G activity ha allowed).mass (insert v s) =
      if u ∈ s then 0 else activity v * (hardCoreWithin G activity ha allowed).mass s := by
  rw [hardCoreWithin_mass_insert G activity ha allowed v hv s hs]
  by_cases hsa : s ⊆ allowed
  · simp only [leaf_unblocked_iff G allowed v u hparent s hsa hs]
    by_cases hu : u ∈ s <;> simp [hu]
  · rw [hardCoreWithin_mass_zero_of_not_subset G activity ha allowed s hsa]
    split_ifs <;> simp

/-- Conditional averaging over the leaf, expressed on the vacant representative of each fiber. -/
noncomputable def leafProjection (b : ℝ) (v u : V) (f : Finset V → ℝ) (s : Finset V) : ℝ :=
  if u ∈ s.erase v then f (s.erase v)
  else (f (s.erase v) + b * f (insert v s)) / (1 + b)

omit [Fintype V] in
theorem leafProjection_erase (b : ℝ) (v u : V) (f : Finset V → ℝ) (s : Finset V) :
    leafProjection b v u f (s.erase v) = leafProjection b v u f s := by
  simp [leafProjection]

theorem hardCoreWithin_leaf_projection (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u)
    (f : Finset V → ℝ) (s : Finset V)
    (hs : 0 < (hardCoreWithin G activity ha allowed).mass s) :
    siteOperator (hardCoreWithin G activity ha allowed) v f s =
      leafProjection (activity v) v u f s := by
  have hse : 0 < (hardCoreWithin G activity ha allowed).mass (s.erase v) := by
    rw [hardCoreWithin_support] at hs ⊢
    exact ⟨(erase_subset v s).trans hs.1, independent_mono G hs.2 (erase_subset v s)⟩
  rw [siteOperator_eq_two _ v f s (fiberMass_pos_of_mass_pos _ v hs).ne']
  have hm := hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent
    (s.erase v) (notMem_erase v s)
  simp only [insert_erase_eq_insert] at hm
  rw [hm]
  unfold leafProjection
  by_cases hu : u ∈ s.erase v
  · simp [hu, hse.ne']
  · simp only [hu, ite_false]
    have he : (hardCoreWithin G activity ha allowed).mass (s.erase v) +
        activity v * (hardCoreWithin G activity ha allowed).mass (s.erase v) =
        (hardCoreWithin G activity ha allowed).mass (s.erase v) * (1 + activity v) := by ring
    rw [he]
    field_simp

theorem hardCoreWithin_leaf_total_variance (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u) (f : Finset V → ℝ) :
    (hardCoreWithin G activity ha allowed).variance f =
      siteConditionalVariance (hardCoreWithin G activity ha allowed) v f +
      (hardCoreWithin G (leafReducedActivity activity v u)
        (leafReducedActivity_pos activity ha v u) (allowed.erase v)).variance
          (leafProjection (activity v) v u f) := by
  rw [← erasedLaw_hardCoreWithin G activity ha allowed v u hv hparent,
    erasedLaw_variance]
  simp_rw [leafProjection_erase]
  rw [← (hardCoreWithin G activity ha allowed).variance_congr_on_support
    (hardCoreWithin_leaf_projection G activity ha allowed v u hv hparent f)]
  rw [siteConditionalVariance_eq_variance_sub]
  ring

end HardCoreActivityThreshold
