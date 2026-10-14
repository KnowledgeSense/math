import SumsetRanges.LevGrowth
import SumsetRanges.LevExclusion

namespace SumsetRanges

/-- No ordinary integer sumset cardinality lies in an excluded interval. -/
theorem card_ordinarySums_not_mem_excludedValues (A : Finset ℤ) (h : ℕ) :
    (ordinarySums A h).card ∉ excludedValues h A.card :=
  card_ordinarySums_not_mem_excludedValues_of_growth A h lev_growth

theorem ordinaryRange_not_mem_excludedValues {h k t : ℕ}
    (ht : t ∈ ordinaryRange h k) : t ∉ excludedValues h k := by
  obtain ⟨A, hA, hAt⟩ := ht
  rw [← hA, ← hAt]
  exact card_ordinarySums_not_mem_excludedValues A h

/-- Rajagopal's exclusion theorem, for actual finite sets of integers. -/
theorem ordinaryRange_inter_excludedValues_eq_empty (h k : ℕ) :
    ordinaryRange h k ∩ (excludedValues h k : Set ℕ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact ordinaryRange_not_mem_excludedValues ht.1 ht.2

end SumsetRanges
