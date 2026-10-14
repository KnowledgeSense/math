import SumsetRanges.OrdinaryThresholdOverlap
import SumsetRanges.OrdinaryTwoRealization

namespace SumsetRanges

/-- Every nonexcluded value in the release's ordinary interval has an actual
 bounded integer witness, at the original polynomial threshold. -/
theorem ordinary_interval_realized (h k t : ℕ) (hh : 2≤h)
    (hk : (2*h)^80≤k) (ht : ordinaryMinimum h k≤t)
    (htop : t≤(h+k-1).choose h) (hex : t∉excludedValues h k) :
    ∃A : Finset ℤ,A.card=k ∧ (∀a∈A,0≤a ∧ a≤(k^(ordinaryExponent h):ℕ)) ∧
      (ordinarySums A h).card=t := by
  rcases Nat.eq_or_lt_of_le hh with he | he
  · subst h
    have hk' : 10≤k := by norm_num at hk; omega
    apply ordinary_two_realized k t hk'
    · unfold ordinaryMinimum at ht; omega
    · simpa [Nat.add_comm] using htop
  · exact ordinary_interval_realized_of_three_le h k t (by omega) hk ht htop hex

end SumsetRanges
