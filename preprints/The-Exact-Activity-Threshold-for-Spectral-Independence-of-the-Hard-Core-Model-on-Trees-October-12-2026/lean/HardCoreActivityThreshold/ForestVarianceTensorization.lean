import HardCoreActivityThreshold.LeafVarianceComparison
import HardCoreActivityThreshold.ForestLeaves
import HardCoreActivityThreshold.GapLower

/-! Uniform approximate variance tensorization for the actual hard-core law on every finite forest. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem leafReducedActivity_small (activity : V → ℝ) (ha : ∀ w, 0 < activity w)
    (hsmall : ∀ w, activity w ≤ 1 / 2) (v u : V) :
    ∀ w, leafReducedActivity activity v u w ≤ 1 / 2 := by
  intro w
  by_cases hw : w = u
  · subst w
    simp only [leafReducedActivity, Function.update_self]
    exact (leaf_activity_le (ha u).le (ha v).le).trans (hsmall u)
  · simpa [leafReducedActivity, hw] using hsmall w

theorem leaf_weighted_variance_step (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2)
    (allowed : Finset V) (v u : V) (hv : v ∈ allowed) (hu : u ∈ allowed)
    (hparent : LeafParent G allowed v u) (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) v f +
      (∑ x ∈ allowed.erase v, leafVarianceWeight (leafReducedActivity activity v u x) *
        siteConditionalVariance (hardCoreWithin G (leafReducedActivity activity v u)
          (leafReducedActivity_pos activity ha v u) (allowed.erase v)) x
            (leafProjection (activity v) v u f)) ≤
      ∑ x ∈ allowed, leafVarianceWeight (activity x) *
        siteConditionalVariance (hardCoreWithin G activity ha allowed) x f := by
  let D (x : V) := siteConditionalVariance (hardCoreWithin G activity ha allowed) x f
  let E (x : V) := siteConditionalVariance (hardCoreWithin G (leafReducedActivity activity v u)
    (leafReducedActivity_pos activity ha v u) (allowed.erase v)) x
      (leafProjection (activity v) v u f)
  have hxcomp (x : V) (hxv : x ≠ v) (hxu : x ≠ u) :
      leafVarianceWeight (leafReducedActivity activity v u x) * E x ≤
        leafVarianceWeight (activity x) * D x := by
    simp only [leafReducedActivity, Function.update_of_ne hxu]
    exact mul_le_mul_of_nonneg_left
      (leaf_siteVariance_nonparent G activity ha allowed v u x hv hparent hxv hxu f)
      (by linarith [leafVarianceWeight_lower (ha x).le (hsmall x)])
  have hsumv := sum_erase_add allowed
    (fun x => leafVarianceWeight (activity x) * D x) hv
  change D v + (∑ x ∈ allowed.erase v, leafVarianceWeight (leafReducedActivity activity v u x) * E x) ≤ _
  by_cases huv : u = v
  · have hsum : (∑ x ∈ allowed.erase v, leafVarianceWeight (leafReducedActivity activity v u x) * E x) ≤
        ∑ x ∈ allowed.erase v, leafVarianceWeight (activity x) * D x := by
      apply sum_le_sum
      intro x hx
      have hxv := (mem_erase.mp hx).1
      exact hxcomp x hxv (by simpa [huv] using hxv)
    have hDv : 0 ≤ D v := siteConditionalVariance_nonneg _ _ _
    have hw := leafVarianceWeight_lower (ha v).le (hsmall v)
    change _ ≤ ∑ x ∈ allowed, leafVarianceWeight (activity x) * D x
    nlinarith
  · have hue : u ∈ allowed.erase v := mem_erase.mpr ⟨huv, hu⟩
    have hsume := sum_erase_add (allowed.erase v)
      (fun x => leafVarianceWeight (leafReducedActivity activity v u x) * E x) hue
    have hsumd := sum_erase_add (allowed.erase v)
      (fun x => leafVarianceWeight (activity x) * D x) hue
    have hsum :
        (∑ x ∈ (allowed.erase v).erase u, leafVarianceWeight (leafReducedActivity activity v u x) * E x) ≤
        ∑ x ∈ (allowed.erase v).erase u, leafVarianceWeight (activity x) * D x := by
      apply sum_le_sum
      intro x hx
      exact hxcomp x (mem_erase.mp (mem_erase.mp hx).2).1 (mem_erase.mp hx).1
    have hp := leaf_siteVariance_parent G activity ha hsmall allowed v u hv hu hparent huv f
    change leafVarianceWeight (activity u / (1 + activity v)) * E u ≤
      leafVarianceWeight (activity u) * D u + (leafVarianceWeight (activity v) - 1) * D v at hp
    rw [show leafReducedActivity activity v u u = activity u / (1 + activity v) by
      simp [leafReducedActivity]] at hsume
    change _ ≤ ∑ x ∈ allowed, leafVarianceWeight (activity x) * D x
    linarith

omit [Fintype V] in
theorem forest_leaf_parent (G : SimpleGraph V) (hG : G.IsAcyclic)
    (allowed : Finset V) (hne : allowed.Nonempty) :
    ∃ v ∈ allowed, ∃ u ∈ allowed, LeafParent G allowed v u := by
  obtain ⟨v, hv, hleaf⟩ := forest_allowed_exists_leaf G hG allowed hne
  by_cases he : ∃ u ∈ allowed, G.Adj v u
  · obtain ⟨u, hu, hvu⟩ := he
    refine ⟨v, hv, u, hu, ?_⟩
    intro w hw _
    constructor
    · intro hvw
      exact hleaf w hw u hu hvw hvu
    · intro hwu
      simpa [hwu] using hvu
  · refine ⟨v, hv, v, hv, ?_⟩
    intro w hw hwv
    constructor
    · intro hvw
      exact False.elim (he ⟨w, hw, hvw⟩)
    · intro hwv'
      exact False.elim (hwv hwv')

/-- Activity-weighted variance tensorization, proved by exact finite leaf elimination. -/
theorem forest_weighted_variance_tensorization (G : SimpleGraph V) (hG : G.IsAcyclic)
    (allowed : Finset V) :
    ∀ (activity : V → ℝ) (ha : ∀ w, 0 < activity w),
      (∀ w, activity w ≤ 1 / 2) → ∀ f : Finset V → ℝ,
      (hardCoreWithin G activity ha allowed).variance f ≤
        ∑ x ∈ allowed, leafVarianceWeight (activity x) *
          siteConditionalVariance (hardCoreWithin G activity ha allowed) x f := by
  refine Finset.strongInductionOn allowed ?_
  intro allowed ih activity ha hsmall f
  rcases allowed.eq_empty_or_nonempty with rfl | hne
  · have hz : (hardCoreWithin G activity ha ∅).variance f = 0 := by
      have he : (hardCoreWithin G activity ha ∅).variance f =
          (hardCoreWithin G activity ha ∅).variance (fun _ => f ∅) := by
        apply FiniteLaw.variance_congr_on_support
        intro s hs
        have hempty := ((hardCoreWithin_support G activity ha ∅ s).mp hs).1
        have hse : s = ∅ := subset_empty.mp hempty
        simp [hse]
      rw [he]
      simp [FiniteLaw.variance]
    simp [hz]
  · obtain ⟨v, hv, u, hu, hparent⟩ := forest_leaf_parent G hG allowed hne
    have hi := ih (allowed.erase v) (erase_ssubset hv)
      (leafReducedActivity activity v u) (leafReducedActivity_pos activity ha v u)
      (leafReducedActivity_small activity ha hsmall v u) (leafProjection (activity v) v u f)
    rw [hardCoreWithin_leaf_total_variance G activity ha allowed v u hv hparent f]
    exact (add_le_add (le_refl _) hi).trans
      (leaf_weighted_variance_step G activity ha hsmall allowed v u hv hu hparent f)

/-- A universal constant of eighteen works for all finite forests at activities at most one half. -/
theorem forest_variance_tensorization (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2)
    (allowed : Finset V) : VarianceTensorization (hardCoreWithin G activity ha allowed) 18 := by
  intro f
  calc
    _ ≤ ∑ x ∈ allowed, leafVarianceWeight (activity x) *
        siteConditionalVariance (hardCoreWithin G activity ha allowed) x f :=
      forest_weighted_variance_tensorization G hG allowed activity ha hsmall f
    _ ≤ ∑ x ∈ allowed, 18 * siteConditionalVariance (hardCoreWithin G activity ha allowed) x f := by
      apply sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (leafVarianceWeight_upper (ha x).le (hsmall x))
        (siteConditionalVariance_nonneg _ _ _)
    _ = 18 * ∑ x ∈ allowed, siteConditionalVariance (hardCoreWithin G activity ha allowed) x f :=
      (mul_sum allowed _ 18).symm
    _ ≤ 18 * ∑ x : V, siteConditionalVariance (hardCoreWithin G activity ha allowed) x f := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg (subset_univ allowed)
        (fun x _ _ => siteConditionalVariance_nonneg _ _ _)

theorem hardCore_forest_variance_tensorization (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2) :
    VarianceTensorization (hardCoreLaw G activity ha) 18 := by
  rw [← hardCoreWithin_univ]
  exact forest_variance_tensorization G hG activity ha hsmall univ

/-- The genuine heat-bath gap has its optimal size dependence at low activity. -/
theorem hardCore_forest_heatBathGap_lower [Nonempty V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (activity : V → ℝ) (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2) :
    1 / (18 * (Fintype.card V : ℝ)) ≤ heatBathGap (hardCoreLaw G activity ha) :=
  (hardCore_forest_variance_tensorization G hG activity ha hsmall).heatBathGap_lower (by norm_num)

end HardCoreActivityThreshold
