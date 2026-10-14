import MainTheorems.AHOConstants.Cuts

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

theorem cutEdges_count_previous (S T : Finset (Fin (m + 1))) :
    (cutEdges S T).card = ∑ i : Fin (m + 1),
      ((if i ∈ S ∧ i ∈ T then (1 : ℕ) else 0) +
        if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then 1 else 0) := by
  have hc : (∑ e : Fin (m + 1) × Bool,
      if aEndpoint e ∈ S ∧ e.1 ∈ T then (1 : ℕ) else 0) = (cutEdges S T).card := by
    rw [← Finset.sum_filter]
    simp [cutEdges]
  have hr : (∑ i : Fin (m + 1),
      if finRotate (m + 1) i ∈ S ∧ i ∈ T then (1 : ℕ) else 0) =
      ∑ i : Fin (m + 1),
        if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then 1 else 0 := by
    simpa only [Equiv.symm_apply_apply] using Equiv.sum_comp (finRotate (m + 1))
      (fun i => if i ∈ S ∧ (finRotate (m + 1)).symm i ∈ T then (1 : ℕ) else 0)
  rw [← hc, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, aEndpoint, Bool.false_eq_true, ite_false, ite_true,
    Finset.sum_add_distrib]
  rw [hr]
  exact add_comm _ _

theorem cut_exponent_sum (p q : Fin (m + 1) → ℝ)
    (hp : (∑ i, p i) = 1) (hq : (∑ i, q i) = 1)
    (S T : Finset (Fin (m + 1))) :
    (∑ i, ((if i ∈ S then 0 else p i) + if i ∈ T then 0 else q i)) =
      2 - cutMass p S - cutMass q T := by
  have hS : ∀ i, (if i ∈ S then 0 else p i) = p i - (if i ∈ S then p i else 0) := by
    intro i
    split_ifs <;> ring
  have hT : ∀ i, (if i ∈ T then 0 else q i) = q i - (if i ∈ T then q i else 0) := by
    intro i
    split_ifs <;> ring
  simp_rw [hS, hT]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp, hq]
  unfold cutMass
  ring

end ResearchMain.AHOConstants
