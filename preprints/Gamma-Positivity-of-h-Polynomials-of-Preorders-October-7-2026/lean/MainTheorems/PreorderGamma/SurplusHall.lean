import MainTheorems.PreorderGamma.Basic

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [Preorder E]

theorem neighborhood_zero_downward (x : E → ℕ) (s : Finset E) :
    neighborhood (zeroSet x) s = (downward s).filter fun a => x a = 0 := by
  classical
  ext a
  simp only [mem_neighborhood, mem_zeroSet, Finset.mem_filter, mem_downward]
  exact and_comm

theorem neighborhood_zero_subset {x : E → ℕ} {s u : Finset E}
    (hu : IsIdeal u) (hs : s ⊆ u) :
    neighborhood (zeroSet x) s ⊆ u.filter fun a => x a = 0 := by
  classical
  intro a ha
  obtain ⟨hzero, b, hb, hab⟩ := mem_neighborhood.mp ha
  exact Finset.mem_filter.mpr ⟨hu (hs hb) hab, mem_zeroSet.mp hzero⟩

theorem isLatticePoint_iff_surplusHall (x : E → ℕ) :
    IsLatticePoint x ↔ SurplusHall x := by
  classical
  constructor
  · intro hx s _hs
    have h := (lattice_inequality_iff_surplus x (downward s)).mp
      (hx (downward s) (downward_isIdeal s))
    have hsum : (∑ a ∈ s, (x a - 1)) ≤ ∑ a ∈ downward s, (x a - 1) :=
      Finset.sum_le_sum_of_subset (subset_downward s)
    rw [neighborhood_zero_downward]
    exact hsum.trans h
  · intro hx u hu
    apply (lattice_inequality_iff_surplus x u).mpr
    let s := u.filter fun a => 2 ≤ x a
    have hs : s ⊆ highSet x := by
      intro a ha
      exact mem_highSet.mpr (Finset.mem_filter.mp ha).2
    have h := hx s hs
    have hn := Finset.card_le_card
      (neighborhood_zero_subset (x := x) (s := s) hu
        (Finset.filter_subset (fun a : E => 2 ≤ x a) u))
    have hsum : (∑ a ∈ s, (x a - 1)) = ∑ a ∈ u, (x a - 1) :=
      sum_high_filter x u
    rw [hsum] at h
    exact h.trans hn

end ResearchMain.PreorderGamma
