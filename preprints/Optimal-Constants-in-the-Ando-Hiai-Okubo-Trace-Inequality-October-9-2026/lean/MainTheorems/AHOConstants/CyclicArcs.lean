import MainTheorems.AHOConstants.Potential

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

def cyclicArc (i j : Fin (m + 1)) : Finset (Fin (m + 1)) :=
  if i.val ≤ j.val then
    Finset.univ.filter (fun t => i.val ≤ t.val ∧ t.val < j.val)
  else
    Finset.univ.filter (fun t => i.val ≤ t.val ∨ t.val < j.val)

theorem sum_indicator (f : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1))) :
    (∑ i ∈ S, f i) = ∑ i, if i ∈ S then f i else 0 := by
  have hS : Finset.univ.filter (fun i => i ∈ S) = S := by
    ext i
    simp
  rw [← Finset.sum_filter, hS]

theorem cyclicArc_empty (i : Fin (m + 1)) : cyclicArc i i = ∅ := by
  ext t
  constructor
  · intro ht
    simp only [cyclicArc, le_refl, ite_true, Finset.mem_filter,
      Finset.mem_univ, true_and] at ht
    omega
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem cyclicArc_start {i j : Fin (m + 1)} (hij : i ≠ j) : i ∈ cyclicArc i j := by
  have hv : i.val ≠ j.val := by exact fun h => hij (Fin.ext h)
  unfold cyclicArc
  split_ifs <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · constructor <;> omega
  · exact Or.inl le_rfl

theorem cyclicArc_finish (i j : Fin (m + 1)) : j ∉ cyclicArc i j := by
  unfold cyclicArc
  split_ifs <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or,
    not_or, not_lt, not_le]
  · exact Or.inr le_rfl
  · constructor <;> omega

theorem cyclicArc_sum (f : Fin (m + 1) → ℝ) (hf : (∑ i, f i) = 0)
    (i j : Fin (m + 1)) :
    (∑ t ∈ cyclicArc i j, f t) =
      (∑ t ∈ Finset.univ.filter (fun t => t.val < j.val), f t) -
      ∑ t ∈ Finset.univ.filter (fun t => t.val < i.val), f t := by
  rw [sum_indicator]
  simp only [Finset.sum_filter]
  by_cases hij : i.val ≤ j.val
  · have hterm : ∀ t : Fin (m + 1),
        (if t ∈ cyclicArc i j then f t else 0) =
        (if t.val < j.val then f t else 0) - (if t.val < i.val then f t else 0) := by
      intro t
      simp only [cyclicArc, hij, ite_true, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> first | omega | ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib]
  · have hterm : ∀ t : Fin (m + 1),
        (if t ∈ cyclicArc i j then f t else 0) = f t +
        (if t.val < j.val then f t else 0) - (if t.val < i.val then f t else 0) := by
      intro t
      simp only [cyclicArc, hij, ite_false, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> first | omega | ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hf]
    ring

theorem cyclicArc_potential_difference (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (i j : Fin (m + 1)) :
    (∑ t ∈ cyclicArc i j, (p (finRotate (m + 1) t) - q t)) =
      cyclicPotential p q j - cyclicPotential p q i := by
  have hf : (∑ t : Fin (m + 1), (p (finRotate (m + 1) t) - q t)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate (m + 1)) p, ht]
    ring
  exact cyclicArc_sum _ hf i j

theorem cyclicArc_rotate {i j : Fin (m + 1)} (hij : i ≠ j) :
    (cyclicArc i j).image (finRotate (m + 1)) = insert j ((cyclicArc i j).erase i) := by
  classical
  ext t
  have hmem : t ∈ (cyclicArc i j).image (finRotate (m + 1)) ↔
      (finRotate (m + 1)).symm t ∈ cyclicArc i j := by
    constructor
    · intro h
      obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
      have he : (finRotate (m + 1)).symm t = s := by
        rw [← hst]
        simp
      rwa [he]
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, (finRotate (m + 1)).apply_symm_apply t⟩
  rw [hmem]
  simp only [Finset.mem_insert, Finset.mem_erase]
  have hi := i.isLt
  have hj := j.isLt
  have ht := t.isLt
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases ht₀ : t = 0
  · subst t
    have hr : (finRotate (m + 1)).symm (0 : Fin (m + 1)) = Fin.last m := by
      apply (finRotate (m + 1)).injective
      simp only [Equiv.apply_symm_apply, finRotate_last]
    rw [hr]
    have hzero : ((0 : Fin (m + 1)) : ℕ) = 0 := rfl
    have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
    simp only [cyclicArc]
    split_ifs <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.ext_iff, Fin.val_zero, Fin.val_last] <;> omega
  · have hv := coe_finRotate_symm_of_ne_zero ht₀
    have htpos : 0 < t.val := by
      have htne : t.val ≠ 0 := fun h => ht₀ (Fin.ext h)
      omega
    simp only [cyclicArc]
    split_ifs <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.ext_iff] <;> rw [hv] <;> omega

end ResearchMain.AHOConstants
