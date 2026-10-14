import HardCoreActivityThreshold.HardCoreSiteFormula
import HardCoreActivityThreshold.LowActivityForest

/-! Local conditional-variance comparisons in the exact leaf-marginalization step. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hardCoreWithin_siteVariance_split (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (x v : V) (hxv : x ≠ v)
    (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) x f =
      ∑ s, if v ∉ s ∧ x ∉ s then
        (hardCoreWithin G activity ha allowed).mass (insert x s) / (1 + activity x) *
          (f s - f (insert x s))^2 +
        (hardCoreWithin G activity ha allowed).mass (insert v (insert x s)) /
          (1 + activity x) * (f (insert v s) - f (insert v (insert x s)))^2 else 0 := by
  rw [hardCoreWithin_siteVariance, sum_config_split v]
  apply sum_congr rfl
  intro s _
  by_cases hv : v ∈ s <;> by_cases hx : x ∈ s <;>
    simp [hv, hx, hxv, insert_comm]

theorem reduced_siteVariance_split (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (x v u : V) (hxv : x ≠ v)
    (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G (leafReducedActivity activity v u)
      (leafReducedActivity_pos activity ha v u) (allowed.erase v)) x f =
      ∑ s, if v ∉ s ∧ x ∉ s then
        (hardCoreWithin G (leafReducedActivity activity v u)
          (leafReducedActivity_pos activity ha v u) (allowed.erase v)).mass (insert x s) /
          (1 + leafReducedActivity activity v u x) * (f s - f (insert x s))^2 else 0 := by
  rw [hardCoreWithin_siteVariance_split G _ _ _ x v hxv]
  simp [hardCoreWithin_insert_mass_zero G _ _ _ v (notMem_erase v allowed)]

theorem reduced_mass (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u)
    (s : Finset V) (hs : v ∉ s) :
    (hardCoreWithin G (leafReducedActivity activity v u)
      (leafReducedActivity_pos activity ha v u) (allowed.erase v)).mass s =
      (if u ∈ s then 1 else 1 + activity v) * (hardCoreWithin G activity ha allowed).mass s := by
  rw [← erasedLaw_hardCoreWithin G activity ha allowed v u hv hparent]
  change (if v ∉ s then _ else _) = _
  simp only [hs, not_false_eq_true, ite_true]
  rw [hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent s hs]
  by_cases hu : u ∈ s
  · simp [hu]
  · simp only [hu, ite_false]
    ring

theorem weighted_average_sq {b : ℝ} (hb : 0 ≤ b) (d e : ℝ) :
    (d + b * e)^2 / (1 + b) ≤ d^2 + b * e^2 := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + b)).mpr
  nlinarith [mul_nonneg hb (sq_nonneg (d - e))]

/-- Averaging a leaf cannot increase a local variance at a different, nonadjacent vertex. -/
theorem leaf_siteVariance_nonparent (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u x : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u)
    (hxv : x ≠ v) (hxu : x ≠ u) (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G (leafReducedActivity activity v u)
      (leafReducedActivity_pos activity ha v u) (allowed.erase v)) x
        (leafProjection (activity v) v u f) ≤
      siteConditionalVariance (hardCoreWithin G activity ha allowed) x f := by
  rw [reduced_siteVariance_split G activity ha allowed x v u hxv,
    hardCoreWithin_siteVariance_split G activity ha allowed x v hxv]
  apply sum_le_sum
  intro s _
  by_cases hs : v ∉ s ∧ x ∉ s
  · simp only [hs, not_false_eq_true, and_self, ite_true]
    have hvx : v ∉ insert x s := by simp [hxv.symm, hs.1]
    rw [reduced_mass G activity ha allowed v u hv hparent (insert x s) hvx,
      hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent (insert x s) hvx]
    simp only [leafReducedActivity, Function.update_of_ne hxu,
      mem_insert, Ne.symm hxu, false_or]
    have he : (insert x s).erase v = insert x s := erase_eq_of_notMem hvx
    simp only [leafProjection, erase_eq_of_notMem hs.1, he,
      mem_insert, Ne.symm hxu, false_or]
    by_cases hu : u ∈ s
    · simp [hu]
    · simp only [hu, ite_false]
      have hd : 1 + activity v ≠ 0 := by linarith [ha v]
      have hh :
          (f s + activity v * f (insert v s)) / (1 + activity v) -
            (f (insert x s) + activity v * f (insert v (insert x s))) / (1 + activity v) =
          ((f s - f (insert x s)) + activity v *
            (f (insert v s) - f (insert v (insert x s)))) / (1 + activity v) := by ring
      rw [hh]
      have heq : (1 + activity v) * (hardCoreWithin G activity ha allowed).mass (insert x s) /
          (1 + activity x) *
          (((f s - f (insert x s)) + activity v *
            (f (insert v s) - f (insert v (insert x s)))) / (1 + activity v))^2 =
          ((hardCoreWithin G activity ha allowed).mass (insert x s) / (1 + activity x)) *
            (((f s - f (insert x s)) + activity v *
              (f (insert v s) - f (insert v (insert x s))))^2 / (1 + activity v)) := by
        field_simp
      rw [heq]
      have hq : 0 ≤ (hardCoreWithin G activity ha allowed).mass (insert x s) / (1 + activity x) :=
        div_nonneg ((hardCoreWithin G activity ha allowed).nonneg _) (by linarith [ha x])
      have hh := mul_le_mul_of_nonneg_left (weighted_average_sq (ha v).le
        (f s - f (insert x s)) (f (insert v s) - f (insert v (insert x s)))) hq
      convert hh using 1
      ring
  · simp [hs]

theorem leaf_siteVariance_split (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u) (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) v f =
      ∑ s, if v ∉ s ∧ u ∉ s then
        (hardCoreWithin G activity ha allowed).mass (insert v s) / (1 + activity v) *
          (f s - f (insert v s))^2 else 0 := by
  rw [hardCoreWithin_siteVariance]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s
  · rw [hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent s hs]
    by_cases hu : u ∈ s <;> simp [hs, hu]
  · simp [hs]

theorem parent_siteVariance_split (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u) (huv : u ≠ v)
    (f : Finset V → ℝ) :
    siteConditionalVariance (hardCoreWithin G activity ha allowed) u f =
      ∑ s, if v ∉ s ∧ u ∉ s then
        (hardCoreWithin G activity ha allowed).mass (insert u s) / (1 + activity u) *
          (f s - f (insert u s))^2 else 0 := by
  rw [hardCoreWithin_siteVariance_split G activity ha allowed u v huv]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s ∧ u ∉ s
  · have hvs : v ∉ insert u s := by simp [huv.symm, hs.1]
    rw [hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent (insert u s) hvs]
    simp [hs]
  · simp [hs]

/-- The changed local variance at the parent is absorbed by its two old endpoint energies. -/
theorem leaf_siteVariance_parent (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (hsmall : ∀ w, activity w ≤ 1 / 2)
    (allowed : Finset V) (v u : V) (hv : v ∈ allowed) (hu : u ∈ allowed)
    (hparent : LeafParent G allowed v u) (huv : u ≠ v) (f : Finset V → ℝ) :
    leafVarianceWeight (activity u / (1 + activity v)) *
      siteConditionalVariance (hardCoreWithin G (leafReducedActivity activity v u)
        (leafReducedActivity_pos activity ha v u) (allowed.erase v)) u
          (leafProjection (activity v) v u f) ≤
      leafVarianceWeight (activity u) *
        siteConditionalVariance (hardCoreWithin G activity ha allowed) u f +
      (leafVarianceWeight (activity v) - 1) *
        siteConditionalVariance (hardCoreWithin G activity ha allowed) v f := by
  rw [reduced_siteVariance_split G activity ha allowed u v u huv,
    parent_siteVariance_split G activity ha allowed v u hv hparent huv,
    leaf_siteVariance_split G activity ha allowed v u hv hparent]
  simp_rw [mul_sum]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro s _
  by_cases hs : v ∉ s ∧ u ∉ s
  · simp only [hs, not_false_eq_true, and_self, ite_true]
    have hvs : v ∉ insert u s := by simp [huv.symm, hs.1]
    rw [reduced_mass G activity ha allowed v u hv hparent (insert u s) hvs,
      hardCoreWithin_leaf_mass G activity ha allowed v u hv hparent s hs.1]
    simp only [mem_insert_self, ite_true, one_mul, leafReducedActivity, Function.update_self]
    simp only [leafProjection, erase_eq_of_notMem hs.1, erase_eq_of_notMem hvs,
      mem_insert_self, ite_true, hs.2, ite_false]
    rw [hardCoreWithin_mass_insert G activity ha allowed u hu s hs.2]
    split_ifs with hfree
    · have hh := mul_le_mul_of_nonneg_left
        (leaf_variance_three_state (ha u).le (hsmall u) (ha v).le (hsmall v)
          (f s) (f (insert v s)) (f (insert u s)))
        ((hardCoreWithin G activity ha allowed).nonneg s)
      have hd : 1 + activity v ≠ 0 := by linarith [ha v]
      have he : 1 + activity u + activity v ≠ 0 := by linarith [ha u, ha v]
      have hf : 1 + activity u / (1 + activity v) ≠ 0 := by
        have hp : 0 < activity u / (1 + activity v) := div_pos (ha u) (by linarith [ha v])
        linarith
      have hcoef : activity u * (hardCoreWithin G activity ha allowed).mass s /
          (1 + activity u / (1 + activity v)) =
          (hardCoreWithin G activity ha allowed).mass s * activity u * (1 + activity v) /
            (1 + activity u + activity v) := by
        field_simp [hd, he, hf]
        ring_nf
        field_simp [he]
        ring
      rw [hcoef]
      convert hh using 1 <;> ring
    · simp only [zero_div, zero_mul, mul_zero, zero_add]
      have hw : 0 ≤ leafVarianceWeight (activity v) - 1 := by
        linarith [leafVarianceWeight_lower (ha v).le (hsmall v)]
      exact mul_nonneg hw (mul_nonneg (div_nonneg
        (mul_nonneg (ha v).le ((hardCoreWithin G activity ha allowed).nonneg s))
        (by linarith [ha v])) (sq_nonneg _))
  · simp [hs]

end HardCoreActivityThreshold
