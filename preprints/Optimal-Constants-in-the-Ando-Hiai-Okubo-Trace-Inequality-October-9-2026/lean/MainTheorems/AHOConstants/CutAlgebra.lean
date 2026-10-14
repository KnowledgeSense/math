import MainTheorems.AHOConstants.Cuts
import MainTheorems.AHOConstants.CyclicArcs

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

theorem cutMass_eq_sum (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1))) :
    cutMass p S = ∑ i ∈ S, p i := (sum_indicator p S).symm

theorem cutMass_complement (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1))) :
    cutMass p Sᶜ = (∑ i, p i) - cutMass p S := by
  have hs : cutMass p Sᶜ + cutMass p S = ∑ i, p i := by
    unfold cutMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  linarith

theorem cutMass_insert (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1)))
    {i : Fin (m + 1)} (hi : i ∉ S) : cutMass p (insert i S) = p i + cutMass p S := by
  rw [cutMass_eq_sum, cutMass_eq_sum, Finset.sum_insert hi]

theorem cutMass_erase (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1)))
    {i : Fin (m + 1)} (hi : i ∈ S) : cutMass p (S.erase i) = cutMass p S - p i := by
  rw [cutMass_eq_sum, cutMass_eq_sum]
  have hs := Finset.sum_erase_add S p hi
  linarith

theorem rotation_mem_image (S : Finset (Fin (m + 1))) (i : Fin (m + 1)) :
    finRotate (m + 1) i ∈ S.image (finRotate (m + 1)) ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    have hji' : j = i := (finRotate (m + 1)).injective hji
    rwa [hji'] at hj
  · intro h
    exact Finset.mem_image.mpr ⟨i, h, rfl⟩

theorem cutMass_rotation (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1))) :
    cutMass p (S.image (finRotate (m + 1))) =
      ∑ i ∈ S, p (finRotate (m + 1) i) := by
  rw [cutMass_eq_sum, Finset.sum_image]
  intro i _ j _ hij
  exact (finRotate (m + 1)).injective hij

theorem arc_cut_mass_difference (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (i j : Fin (m + 1)) :
    cutMass p ((cyclicArc i j).image (finRotate (m + 1))) - cutMass q (cyclicArc i j) =
      cyclicPotential p q j - cyclicPotential p q i := by
  rw [cutMass_rotation, cutMass_eq_sum, ← Finset.sum_sub_distrib]
  exact cyclicArc_potential_difference p q ht i j

theorem arc_cut_edges_one {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutEdges ((cyclicArc i j).image (finRotate (m + 1))) (cyclicArc i j)ᶜ =
      {(j, false)} := by
  have hj := cyclicArc_finish i j
  ext e
  rcases e with ⟨x, b⟩
  cases b
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, Bool.false_eq_true, ite_false, Finset.mem_compl,
      cyclicArc_rotate hij, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_singleton, Prod.mk.injEq, and_true]
    constructor
    · rintro ⟨hx, hn⟩
      rcases hx with hx | hx
      · exact hx
      · exact False.elim (hn hx.2)
    · intro hx
      subst x
      exact ⟨Or.inl rfl, hj⟩
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, ite_true, rotation_mem_image, Finset.mem_compl,
      Finset.mem_singleton, Prod.mk.injEq, Bool.true_eq_false, and_false]
    tauto

theorem arc_cut_edges_zero {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutEdges ((cyclicArc i j).image (finRotate (m + 1))) (insert j (cyclicArc i j))ᶜ = ∅ := by
  ext e
  rcases e with ⟨x, b⟩
  cases b
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, Bool.false_eq_true, ite_false, Finset.mem_compl,
      cyclicArc_rotate hij, Finset.mem_insert, Finset.mem_erase, Finset.notMem_empty]
    tauto
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, ite_true, rotation_mem_image, Finset.mem_compl,
      Finset.mem_insert, Finset.notMem_empty]
    tauto

theorem arc_cut_edges_other_one {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutEdges ((cyclicArc i j).image (finRotate (m + 1)))
      (insert j ((cyclicArc i j).erase i))ᶜ = {(i, true)} := by
  have hi := cyclicArc_start hij
  ext e
  rcases e with ⟨x, b⟩
  cases b
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, Bool.false_eq_true, ite_false, Finset.mem_compl,
      cyclicArc_rotate hij, Finset.mem_singleton, Prod.mk.injEq, Bool.false_eq_true, and_false]
    tauto
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, ite_true, rotation_mem_image, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Prod.mk.injEq, and_true]
    constructor
    · rintro ⟨hx, hn⟩
      by_contra hxi
      exact hn (Or.inr ⟨hxi, hx⟩)
    · intro hxi
      subst x
      exact ⟨hi, by simp [hij]⟩

theorem arc_cut_edges_two {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutEdges ((cyclicArc i j).image (finRotate (m + 1))) ((cyclicArc i j).erase i)ᶜ =
      {(j, false), (i, true)} := by
  have hi := cyclicArc_start hij
  have hj := cyclicArc_finish i j
  ext e
  rcases e with ⟨x, b⟩
  cases b
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, Bool.false_eq_true, ite_false, Finset.mem_compl,
      cyclicArc_rotate hij, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_singleton, Prod.mk.injEq, Bool.false_eq_true, and_false,
      and_true, or_false]
    constructor
    · rintro ⟨hx, hn⟩
      rcases hx with hx | hx
      · exact hx
      · exact False.elim (hn hx)
    · intro hx
      subst x
      exact ⟨Or.inl rfl, by simp [hj]⟩
  · simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      aEndpoint, ite_true, rotation_mem_image, Finset.mem_compl,
      Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Prod.mk.injEq, Bool.true_eq_false, and_false, and_true, false_or]
    constructor
    · rintro ⟨hx, hn⟩
      by_contra hxi
      exact hn ⟨hxi, hx⟩
    · intro hxi
      subst x
      exact ⟨hi, by simp⟩

end ResearchMain.AHOConstants
