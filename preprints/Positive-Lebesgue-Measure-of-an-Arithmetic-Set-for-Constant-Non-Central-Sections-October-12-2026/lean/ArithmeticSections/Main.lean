import ArithmeticSections.LocalConditions
import ArithmeticSections.CylinderExclusions
import ArithmeticSections.CylinderShrinking

namespace ArithmeticSections
open MeasureTheory
open scoped Topology

/-- The main theorem of the release: every neighborhood of the exact explicit A₀
contains a Borel subset of the actual arithmetic set of positive Lebesgue measure. -/
theorem positive_measure_in_every_neighborhood {W : Set ℝ} (hW : W ∈ 𝓝 seedVolume) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ arithmeticSet ∩ W ∧ 0 < volume E := by
  have hseed : seedDoubledRotation ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [seedDoubledRotation_eq]
    constructor <;> linarith [seedRotation_bounds.1, seedRotation_bounds.2]
  obtain ⟨L, hL, hcyl⟩ := exists_digitCylinder_subset_nhds seedDoubledRotation_irrational hseed
    (finiteConditionRegion_mem_nhds hW) 256
  let E := boundedTailCylinder (actualDigit seedDoubledRotation) L
  have hmeas : MeasurableSet E := measurableSet_boundedTailCylinder _ _
  have hdom : E ⊆ Set.Ioo (0 : ℝ) 1 := fun _ h => h.1.2.1
  have hpos : 0 < volume E :=
    volume_boundedTailCylinder_pos (one_le_actualDigit_succ seedDoubledRotation_irrational) (by omega)
  obtain ⟨hmeasA, hposA⟩ := volume_image_positive hmeas hdom hpos
  refine ⟨doubledVolumeCoordinate '' E, hmeasA, ?_, hposA⟩
  rintro A ⟨θ, hθ, rfl⟩
  exact volume_mem_of_bounded_seed_cylinder hL hθ (hcyl hθ.1)

/-- In particular, the original arithmetic set has positive Lebesgue measure. -/
theorem arithmeticSet_positive_volume : 0 < volume arithmeticSet := by
  obtain ⟨E, _, hE, hpos⟩ := positive_measure_in_every_neighborhood
    (W := Set.univ) Filter.univ_mem
  exact hpos.trans_le (measure_mono (fun x hx => (hE hx).1))

end ArithmeticSections
