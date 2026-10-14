import MainTheorems.AHOConstants.CutAlgebra

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

theorem arc_capacity_first (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (hq : (∑ i, q i) = 1)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutCapacity p q ((cyclicArc i j).image (finRotate (m + 1))) (cyclicArc i j)ᶜ =
      3 / 2 - (cyclicPotential p q j - cyclicPotential p q i) := by
  have hd := arc_cut_mass_difference p q ht i j
  have hc := cutMass_complement q (cyclicArc i j)
  rw [hq] at hc
  unfold cutCapacity
  rw [arc_cut_edges_one hij]
  simp only [Finset.card_singleton, Nat.cast_one]
  linarith

theorem arc_capacity_zero (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (hq : (∑ i, q i) = 1)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutCapacity p q ((cyclicArc i j).image (finRotate (m + 1)))
      (insert j (cyclicArc i j))ᶜ =
      1 - (cyclicPotential p q j - cyclicPotential p q i) + q j := by
  have hd := arc_cut_mass_difference p q ht i j
  have hc := cutMass_complement q (insert j (cyclicArc i j))
  rw [hq, cutMass_insert q (cyclicArc i j) (cyclicArc_finish i j)] at hc
  unfold cutCapacity
  rw [arc_cut_edges_zero hij]
  simp only [Finset.card_empty, Nat.cast_zero, zero_div, add_zero]
  linarith

theorem arc_capacity_second (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (hq : (∑ i, q i) = 1)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutCapacity p q ((cyclicArc i j).image (finRotate (m + 1)))
      (insert j ((cyclicArc i j).erase i))ᶜ =
      3 / 2 - (cyclicPotential p q j - cyclicPotential p q i) - q i + q j := by
  have hd := arc_cut_mass_difference p q ht i j
  have hj : j ∉ (cyclicArc i j).erase i := by simp [cyclicArc_finish i j]
  have hc := cutMass_complement q (insert j ((cyclicArc i j).erase i))
  rw [hq, cutMass_insert q ((cyclicArc i j).erase i) hj,
    cutMass_erase q (cyclicArc i j) (cyclicArc_start hij)] at hc
  unfold cutCapacity
  rw [arc_cut_edges_other_one hij]
  simp only [Finset.card_singleton, Nat.cast_one]
  linarith

theorem arc_capacity_two (p q : Fin (m + 1) → ℝ)
    (ht : (∑ i, p i) = ∑ i, q i) (hq : (∑ i, q i) = 1)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    cutCapacity p q ((cyclicArc i j).image (finRotate (m + 1)))
      ((cyclicArc i j).erase i)ᶜ =
      2 - (cyclicPotential p q j - cyclicPotential p q i) - q i := by
  have hd := arc_cut_mass_difference p q ht i j
  have hc := cutMass_complement q ((cyclicArc i j).erase i)
  rw [hq, cutMass_erase q (cyclicArc i j) (cyclicArc_start hij)] at hc
  unfold cutCapacity
  rw [arc_cut_edges_two hij]
  norm_num
  norm_num at hc
  linarith

end ResearchMain.AHOConstants
