import SumsetRanges.OrdinaryRealization
import SumsetRanges.OrdinaryExclusion
import SumsetRanges.OrdinaryLowerBound
import SumsetRanges.OrdinaryUpperBound

namespace SumsetRanges

/-- Exact ordinary-sumset classification beyond the original polynomial threshold. -/
theorem ordinary_range_eq (h k : ℕ) (hh : 2 ≤ h) (hk : (2*h)^80 ≤ k) :
    ordinaryRange h k =
      Set.Icc (ordinaryMinimum h k) ((h+k-1).choose h) \ (excludedValues h k : Set ℕ) := by
  apply Set.Subset.antisymm
  · intro t ht
    have hex := ordinaryRange_not_mem_excludedValues ht
    obtain ⟨A, hA, hAt⟩ := ht
    have hkpos : 0 < k := by
      have he := ordinary_threshold_elementary h k hh hk
      omega
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    have hlo := ordinaryMinimum_le_card A hne h
    have hhi := card_ordinarySums_le A h
    rw [hA, hAt] at hlo hhi
    refine ⟨⟨hlo, ?_⟩, hex⟩
    simpa only [Nat.add_comm k h] using hhi
  · intro t ht
    obtain ⟨A, hA, _, hAt⟩ :=
      ordinary_interval_realized h k t hh hk ht.1.1 ht.1.2 ht.2
    exact ⟨A, hA, hAt⟩

/-- The ordinary main theorem, including the original exponent and witness interval. -/
theorem ordinary_main : OrdinaryMainStatement := by
  intro h k hh hk
  refine ⟨ordinary_range_eq h k hh hk, ?_⟩
  intro t ht
  exact ordinary_interval_realized h k t hh hk ht.1.1 ht.1.2 ht.2

end SumsetRanges
