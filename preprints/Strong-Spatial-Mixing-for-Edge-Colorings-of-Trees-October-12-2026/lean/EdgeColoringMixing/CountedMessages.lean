import EdgeColoringMixing.ChildTree

set_option autoImplicit false

/-! Invariant-domain bounds for exact messages defined by actual coloring counts. -/
namespace EdgeColoringMixing
open Finset WeightedInjection
attribute [local instance] Classical.propDecidable

theorem availabilityStep_eq_of_partition_pos {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (hn : ∀ i c, 0 ≤ maskedWeights F A i c)
    (hZ : 0 < partition (maskedWeights F A)) (c : Fin q) :
    availabilityStep F A c =
      (if c ∈ F then 0 else 1) - colorMean (law _ hn hZ) c := by
  classical
  by_cases hc : c ∈ F
  · have hz := colorMean_eq_zero_of_column_zero _ hn hZ c
      (fun i => by simp [maskedWeights, hc])
    simp [availabilityStep, hc, hz]
  · simp only [availabilityStep, hc, ite_false]
    exact color_unused_probability _ hn hZ c

theorem availabilityStep_unit_interval {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (hn : ∀ i c, 0 ≤ maskedWeights F A i c)
    (hZ : 0 < partition (maskedWeights F A)) (c : Fin q) :
    0 ≤ availabilityStep F A c ∧ availabilityStep F A c ≤ 1 := by
  classical
  by_cases hc : c ∈ F
  · simp [availabilityStep, hc]
  · rw [availabilityStep_eq_of_partition_pos F A hn hZ c, ite_eq_right hc]
    exact ⟨by linarith [colorMean_le_one (law _ hn hZ) c],
      by linarith [colorMean_nonneg (law _ hn hZ) c]⟩

theorem availabilityStep_mass_of_partition_pos {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (hn : ∀ i c, 0 ≤ maskedWeights F A i c)
    (hZ : 0 < partition (maskedWeights F A)) :
    (∑ c, availabilityStep F A c) = (q : ℝ) - F.card - d := by
  classical
  simp_rw [availabilityStep_eq_of_partition_pos F A hn hZ]
  rw [Finset.sum_sub_distrib, colorMean_total]
  have hp : (∑ c : Fin q, if c ∈ F then (1 : ℝ) else 0) = (F.card : ℝ) := by simp
  have hpoint (c : Fin q) : (if c ∈ F then (0 : ℝ) else 1) =
      1 - if c ∈ F then 1 else 0 := by
    by_cases hc : c ∈ F <;> simp [hc]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hp]
  simp

namespace RootedCounting
universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Exact counting availabilities are nonnegative before imposing any degree bound. -/
theorem childAvailability_nonneg (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (i : G.neighborSet r) (c : Fin q) :
    0 ≤ childAvailability hG r q F i c := by
  unfold childAvailability
  positivity

/-- Positivity of the exact root partition follows from feasibility of the original tree. -/
theorem counted_partition_pos (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) {d : ℕ}
    (e : Fin d ≃ G.neighborSet r) :
    0 < partition (maskedWeights (F r) (fun j => childAvailability hG r q F (e j))) := by
  have hW : maskedWeights (F r) (fun j => childAvailability hG r q F (e j)) =
      (fun j => rootWeight hG r q F (e j)) := rfl
  rw [hW, partition_reindex_finite e, root_partition_eq hG r q F]
  apply div_pos
  · exact_mod_cast Fintype.card_pos_iff.mpr hfull
  · apply Finset.prod_pos
    intro i _
    exact_mod_cast Fintype.card_pos_iff.mpr (branch_nonempty hG r q F hfull i)

theorem counted_weights_nonneg (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) {d : ℕ} (e : Fin d ≃ G.neighborSet r) :
    ∀ i c, 0 ≤ maskedWeights (F r) (fun j => childAvailability hG r q F (e j)) i c := by
  intro i c
  unfold maskedWeights
  split_ifs
  · rfl
  · exact childAvailability_nonneg hG r q F _ c

/-- Exact counting messages belong to [0,1] on every color. -/
theorem rootAvailability_unit_interval (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) (c : Fin q) :
    0 ≤ rootAvailability (G := G) r q F c ∧ rootAvailability (G := G) r q F c ≤ 1 := by
  let e := (Fintype.equivFin (G.neighborSet r)).symm
  rw [rootAvailability_recursion hG r q F hfull e c]
  exact availabilityStep_unit_interval _ _ (counted_weights_nonneg hG r q F e)
    (counted_partition_pos hG r q F hfull e) c

/-- The exact availability mass counts unused colors, not an assumed inductive surrogate. -/
theorem rootAvailability_mass (hG : G.IsTree) (r : V) (q : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) :
    (∑ c, rootAvailability (G := G) r q F c) =
      (q : ℝ) - (F r).card - Fintype.card (G.neighborSet r) := by
  let e := (Fintype.equivFin (G.neighborSet r)).symm
  simp_rw [rootAvailability_recursion hG r q F hfull e]
  exact availabilityStep_mass_of_partition_pos _ _ (counted_weights_nonneg hG r q F e)
    (counted_partition_pos hG r q F hfull e)

/-- Every genuine directed-subtree message is in the original invariant domain. -/
theorem rootAvailability_mem_domain (hG : G.IsTree) (r : V) (q Δ : ℕ)
    (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F))
    (hdegree : (F r).card + Fintype.card (G.neighborSet r) + 1 ≤ Δ) :
    MessageDomain Δ q (rootAvailability (G := G) r q F) := by
  refine ⟨fun c => (rootAvailability_unit_interval hG r q F hfull c).1,
    fun c => (rootAvailability_unit_interval hG r q F hfull c).2, ?_⟩
  rw [rootAvailability_mass hG r q F hfull]
  have hd : ((F r).card : ℝ) + Fintype.card (G.neighborSet r) + 1 ≤ Δ := by
    exact_mod_cast hdegree
  linarith

end RootedCounting
end EdgeColoringMixing
