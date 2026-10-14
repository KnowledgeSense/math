import HardCoreActivityThreshold.GapConstants
import HardCoreActivityThreshold.PinnedForestTensorization

/-! The uniform heat-bath lower bound from an actual forest correlation estimate. -/
namespace HardCoreActivityThreshold
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Small-activity tensorization and finite revealing convert a uniform field/pinning
correlation estimate into the genuine heat-bath lower bound, without an external mixing axiom. -/
theorem hardCore_forest_gap_of_field_correlation (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ v, 0 < activity v) {Λ B : ℝ}
    (hcap : ∀ v, activity v ≤ Λ)
    (hcorr : ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 → ∀ (r : Finset V)
      (hr : 0 < (applyField (hardCoreLaw G activity ha) (fun _ => x)
        (fun _ => hx)).eventMass (agreesWith r r)),
      CorrelationBound ((applyField (hardCoreLaw G activity ha) (fun _ => x)
        (fun _ => hx)).condition (agreesWith r r) hr) B) :
    boostedForestGapConstant Λ B / Fintype.card V ≤ heatBathGap (hardCoreLaw G activity ha) := by
  apply heatBathGap_lower_of_field_bounds (hardCoreLaw G activity ha)
    (halfActivityField_pos Λ) (halfActivityField_lt_one Λ) (by norm_num : (1 : ℝ) ≤ 18) hcorr
  intro r hr
  have hsmall : ∀ v, activity v * halfActivityField Λ ≤ 1 / 2 := by
    intro v
    rw [mul_comm]
    exact halfActivityField_mul_le_half Λ (activity v) (hcap v)
  have he := applyField_hardCore G activity (fun _ => halfActivityField Λ) ha
    (fun _ => halfActivityField_pos Λ)
  revert hr
  rw [he]
  intro hr
  exact pinned_forest_variance_tensorization G hG
    (fun v => activity v * halfActivityField Λ)
    (fun v => mul_pos (ha v) (halfActivityField_pos Λ)) hsmall r r hr

end HardCoreActivityThreshold
