import ArithmeticSections.VolumeCoordinates
import ArithmeticSections.CylinderSemantics

namespace ArithmeticSections
open MeasureTheory Filter
open scoped Topology

theorem seedDoubledRotation_half : seedDoubledRotation / 2 = seedRotation := by
  rw [seedDoubledRotation_eq]
  ring

theorem doubledVolumeCoordinate_seed : doubledVolumeCoordinate seedDoubledRotation = seedVolume := by
  rw [doubledVolumeCoordinate, seedDoubledRotation_half, seedVolume_eq]

noncomputable def seedThreshold : ℕ := actualDenominator seedDoubledRotation 256

/-- The finitely many strict inequalities needed before the universal digit tail begins. -/
def finiteConditionRegion (W : Set ℝ) : Set ℝ := {θ | (2 / 3 : ℝ) < θ ∧ θ < 1 ∧
  8 * omegaThree < doubledVolumeCoordinate θ ∧ doubledVolumeCoordinate θ ∈ W ∧
  ∀ k : ℕ, 2 ≤ k → k < seedThreshold → 0 < conditionGap (θ / 2) k}

theorem finiteConditionRegion_mem_nhds {W : Set ℝ} (hW : W ∈ 𝓝 seedVolume) :
    finiteConditionRegion W ∈ 𝓝 seedDoubledRotation := by
  have hseed : seedDoubledRotation ∈ Set.Ioo (2 / 3 : ℝ) 1 := by
    rw [seedDoubledRotation_eq]
    constructor <;> linarith [seedRotation_bounds.1, seedRotation_bounds.2]
  have hc := continuousAt_doubledVolumeCoordinate (by linarith [hseed.1] : 0 < seedDoubledRotation) hseed.2
  have hw : ∀ᶠ θ in 𝓝 seedDoubledRotation, doubledVolumeCoordinate θ ∈ W := by
    apply hc.preimage_mem_nhds
    simpa only [doubledVolumeCoordinate_seed] using hW
  have hv : ∀ᶠ θ in 𝓝 seedDoubledRotation, 8 * omegaThree < doubledVolumeCoordinate θ := by
    apply continuous_const.continuousAt.eventually_lt hc
    simpa only [doubledVolumeCoordinate_seed] using seedVolume_threshold
  have hf : ∀ᶠ θ in 𝓝 seedDoubledRotation, ∀ k ∈ Finset.range seedThreshold,
      2 ≤ k → 0 < conditionGap (θ / 2) k := by
    rw [Filter.eventually_all_finset]
    intro k _
    by_cases hk : 2 ≤ k
    · have hgap : ContinuousAt (fun θ : ℝ => conditionGap (θ / 2) k) seedDoubledRotation := by
        have hh : ContinuousAt (fun γ : ℝ => conditionGap γ k) (seedDoubledRotation / 2) := by
          rw [seedDoubledRotation_half]
          exact continuousAt_conditionGap seedRotation_irrational seedRotation_bounds.1 seedRotation_bounds.2 hk
        exact ContinuousAt.comp (f := fun θ : ℝ => θ / 2) hh (continuous_id.continuousAt.div_const 2)
      have hpos : (0 : ℝ) < conditionGap (seedDoubledRotation / 2) k := by
        rw [seedDoubledRotation_half]
        exact seed_all_conditions k hk
      filter_upwards [continuous_const.continuousAt.eventually_lt hgap hpos] with θ hθ
      exact fun _ => hθ
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hk h))
  have hd : ∀ᶠ θ in 𝓝 seedDoubledRotation, θ ∈ Set.Ioo (2 / 3 : ℝ) 1 := isOpen_Ioo.mem_nhds hseed
  filter_upwards [hd, hv, hw, hf] with θ hθ hv hw hf
  exact ⟨hθ.1, hθ.2, hv, hw, fun k hk hk' => hf k (Finset.mem_range.mpr hk') hk⟩

/-- Actual prefix agreement and the proved tail criterion give membership in the original set. -/
theorem volume_mem_of_bounded_seed_cylinder {W : Set ℝ} {L : ℕ} (hL : 256 ≤ L)
    {θ : ℝ} (hθ : θ ∈ boundedTailCylinder (actualDigit seedDoubledRotation) L)
    (hlocal : θ ∈ finiteConditionRegion W) :
    doubledVolumeCoordinate θ ∈ arithmeticSet ∩ W := by
  have hirr : Irrational θ := hθ.1.1
  have hgirr : Irrational (θ / 2) := by
    simpa using hirr.div_ratCast (q := 2) (by norm_num)
  have hγlo : 1 / 3 < θ / 2 := by linarith [hlocal.1]
  have hγhi : θ / 2 < 1 / 2 := by linarith [hlocal.2.1]
  have hinv : rotationOfVolume (doubledVolumeCoordinate θ) = θ / 2 :=
    rotationOfVolume_volumeCoordinate (by linarith) hγhi
  have hq : actualDenominator θ 256 = seedThreshold :=
    actualDenominator_eq_of_mem_digitCylinder hθ.1 hL
  have hdigit : ∀ l, 257 ≤ l → actualDigit θ l ≤ l ^ 2 := by
    intro l hl
    by_cases hle : l ≤ L
    · rw [hθ.1.2.2 l (by omega) hle]
      exact seed_actualDigit_le_square l
    · exact hθ.2 l (by omega)
  refine ⟨⟨hlocal.2.2.1, ?_, ?_⟩, hlocal.2.2.2.1⟩
  · rwa [hinv]
  · intro k hk
    rw [hinv]
    by_cases hsmall : k < seedThreshold
    · exact hlocal.2.2.2.2 k hk hsmall
    · apply polynomial_digit_tail hgirr hγlo hγhi
      · simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hdigit
      · rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), hq]
        omega

end ArithmeticSections
