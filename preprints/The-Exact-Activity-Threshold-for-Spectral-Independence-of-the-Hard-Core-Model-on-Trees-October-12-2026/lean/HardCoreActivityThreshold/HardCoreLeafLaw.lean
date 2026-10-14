import HardCoreActivityThreshold.ErasedLaw
import HardCoreActivityThreshold.RestrictedLaw
import HardCoreActivityThreshold.Pinning
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact marginal laws for deleting a leaf from a heterogeneous hard-core measure. -/
namespace HardCoreActivityThreshold
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem independent_insert_iff (G : SimpleGraph V) (v : V) (s : Finset V) :
    Independent G (insert v s) ↔ Independent G s ∧ ∀ w ∈ s, ¬ G.Adj v w := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x (mem_insert_of_mem hx) y (mem_insert_of_mem hy),
      fun w hw => h v (mem_insert_self _ _) w (mem_insert_of_mem hw)⟩
  · rintro ⟨hs, hv⟩ x hx y hy
    rcases mem_insert.mp hx with hxv | hx
    · subst x
      rcases mem_insert.mp hy with hyv | hy
      · subst y
        exact G.loopless.irrefl _
      · exact hv y hy
    · rcases mem_insert.mp hy with hyv | hy
      · subst y
        exact fun h => hv x hx h.symm
      · exact hs x hx y hy

theorem withinWeight_insert (G : SimpleGraph V) (activity : V → ℝ)
    (allowed s : Finset V) (v : V) (hv : v ∈ allowed) (hs : v ∉ s) :
    withinWeight G activity allowed (insert v s) =
      if ∀ w ∈ s, ¬ G.Adj v w then activity v * withinWeight G activity allowed s else 0 := by
  unfold withinWeight configurationWeight
  rw [independent_insert_iff]
  simp only [insert_subset_iff, hv, true_and, prod_insert hs]
  by_cases ha : s ⊆ allowed <;> by_cases hi : Independent G s <;>
    by_cases hn : ∀ w ∈ s, ¬ G.Adj v w <;> simp [ha, hi, hn]

/-- The selected parent may equal the deleted vertex when that vertex is isolated. -/
def LeafParent (G : SimpleGraph V) (allowed : Finset V) (v u : V) : Prop :=
  ∀ w ∈ allowed, w ≠ v → (G.Adj v w ↔ w = u)

omit [Fintype V] [DecidableEq V] in
theorem leaf_unblocked_iff (G : SimpleGraph V) (allowed : Finset V) (v u : V)
    (hparent : LeafParent G allowed v u) (s : Finset V)
    (hs : s ⊆ allowed) (hv : v ∉ s) :
    (∀ w ∈ s, ¬ G.Adj v w) ↔ u ∉ s := by
  constructor
  · intro h hu
    exact h u hu ((hparent u (hs hu) (fun he => hv (he ▸ hu))).mpr rfl)
  · intro hu w hw h
    exact hu ((hparent w (hs hw) (fun he => hv (he ▸ hw))).mp h ▸ hw)

noncomputable def leafReducedActivity (activity : V → ℝ) (v u : V) : V → ℝ :=
  Function.update activity u (activity u / (1 + activity v))

omit [Fintype V] in
theorem leafReducedActivity_pos (activity : V → ℝ) (ha : ∀ w, 0 < activity w)
    (v u : V) : ∀ w, 0 < leafReducedActivity activity v u w := by
  intro w
  by_cases hw : w = u
  · subst w
    simp only [leafReducedActivity, Function.update_self]
    exact div_pos (ha u) (by linarith [ha v])
  · simpa [leafReducedActivity, hw] using ha w

omit [Fintype V] in
theorem withinWeight_leafReduced (G : SimpleGraph V) (activity : V → ℝ)
    (allowed s : Finset V) (v u : V) :
    withinWeight G (leafReducedActivity activity v u) allowed s =
      if u ∈ s then withinWeight G activity allowed s / (1 + activity v)
      else withinWeight G activity allowed s := by
  unfold withinWeight configurationWeight
  by_cases hs : s ⊆ allowed <;> by_cases hi : Independent G s <;>
    simp only [hs, hi, ite_true, ite_false]
  · by_cases hu : u ∈ s
    · simp only [hu, ite_true, leafReducedActivity, prod_update_of_mem hu, sdiff_singleton_eq_erase]
      rw [← mul_prod_erase s activity hu]
      ring
    · simp only [hu, ite_false, leafReducedActivity, prod_update_of_notMem hu]
  all_goals split_ifs <;> simp

theorem leaf_weight_pair (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u)
    (s : Finset V) (hs : v ∉ s) :
    withinWeight G activity allowed s + withinWeight G activity allowed (insert v s) =
      (1 + activity v) * withinWeight G (leafReducedActivity activity v u) (allowed.erase v) s := by
  rw [withinWeight_insert G activity allowed s v hv hs, withinWeight_leafReduced]
  have he : withinWeight G activity (allowed.erase v) s = withinWeight G activity allowed s := by
    unfold withinWeight
    simp [subset_erase, hs]
  rw [he]
  by_cases hsa : s ⊆ allowed
  · simp only [leaf_unblocked_iff G allowed v u hparent s hsa hs]
    by_cases hu : u ∈ s
    · simp only [hu, not_true_eq_false, ite_false, ite_true, add_zero]
      exact (mul_div_cancel₀ _ (by linarith [ha v] : 1 + activity v ≠ 0)).symm
    · simp [hu]
      ring
  · simp [withinWeight, hsa]

theorem leaf_partition (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u) :
    partitionWithin G activity allowed = (1 + activity v) *
      partitionWithin G (leafReducedActivity activity v u) (allowed.erase v) := by
  rw [← withinWeight_sum, ← withinWeight_sum, mul_sum, sum_config_split v]
  apply sum_congr rfl
  intro s _
  by_cases hs : v ∉ s
  · simpa only [hs, not_false_eq_true, ite_true] using
      leaf_weight_pair G activity ha allowed v u hv hparent s hs
  · have hn : ¬ s ⊆ allowed.erase v := by
      intro h
      exact notMem_erase v allowed (h (not_not.mp hs))
    simp [hs, withinWeight, hn]

/-- The deleted-coordinate marginal is exactly another hard-core law, with one reduced activity. -/
theorem erasedLaw_hardCoreWithin (G : SimpleGraph V) (activity : V → ℝ)
    (ha : ∀ w, 0 < activity w) (allowed : Finset V) (v u : V)
    (hv : v ∈ allowed) (hparent : LeafParent G allowed v u) :
    erasedLaw (hardCoreWithin G activity ha allowed) v =
      hardCoreWithin G (leafReducedActivity activity v u)
        (leafReducedActivity_pos activity ha v u) (allowed.erase v) := by
  apply FiniteLaw.ext
  intro s
  by_cases hs : v ∉ s
  · change (if v ∉ s then _ else _) = _
    simp only [hs, not_false_eq_true, ite_true, hardCoreWithin]
    rw [← add_div, leaf_weight_pair G activity ha allowed v u hv hparent s hs,
      leaf_partition G activity ha allowed v u hv hparent]
    exact mul_div_mul_left _ _ (by linarith [ha v] : 1 + activity v ≠ 0)
  · have hn : ¬ s ⊆ allowed.erase v := by
      intro h
      exact notMem_erase v allowed (h (not_not.mp hs))
    simp [erasedLaw, hardCoreWithin, hs, withinWeight, hn]

end HardCoreActivityThreshold
