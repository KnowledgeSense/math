import BuchweitzProfiles.Definitions

namespace BuchweitzProfiles

variable {m : Nat} {C : Nat → Prop}

theorem gap_lt_twice (hm : 3 ≤ m) (_hC : ∀ c, C c → c ≤ m - 2)
    {n : Nat} (hn : ReflectedGap m C n) : n < 2 * m := by
  rcases hn with ⟨_, hn⟩ | ⟨c, hc, hn⟩
  · omega
  · omega

theorem positive_nongap_ge (hn : ¬ ReflectedGap m C n) (hp : 0 < n) : m ≤ n := by
  by_cases h : m ≤ n
  · exact h
  · exact False.elim (hn (Or.inl (by omega)))

/-- The semigroup is the actual complement of the reflected gapset. -/
def depthTwoSemigroup (hm : 3 ≤ m) (hC : ∀ c, C c → c ≤ m - 2) :
    NumericalSemigroup where
  carrier n := ¬ ReflectedGap m C n
  zero_mem := by
    rintro (⟨h, _⟩ | ⟨c, hc, he⟩)
    · omega
    · have := hC c hc; omega
  add_mem := by
    intro a b ha hb
    by_cases hza : a = 0
    · simpa [hza] using hb
    by_cases hzb : b = 0
    · simpa [hzb] using ha
    have hma := positive_nongap_ge ha (by omega)
    have hmb := positive_nongap_ge hb (by omega)
    intro hg
    have := gap_lt_twice hm hC hg
    omega
  cofinite := by
    refine ⟨2 * m, ?_⟩
    intro n hn hg
    have := gap_lt_twice hm hC hg
    omega

@[simp] theorem mem_depthTwoSemigroup (hm : 3 ≤ m)
    (hC : ∀ c, C c → c ≤ m - 2) (n : Nat) :
    n ∈ depthTwoSemigroup hm hC ↔ ¬ ReflectedGap m C n := Iff.rfl

theorem depthTwo_multiplicity (hm : 3 ≤ m) (hC : ∀ c, C c → c ≤ m - 2) :
    IsMultiplicity (depthTwoSemigroup hm hC) m := by
  refine ⟨by omega, ?_, ?_⟩
  · rintro (⟨_, h⟩ | ⟨c, hc, he⟩)
    · omega
    · have := hC c hc; omega
  · intro n hn hp
    exact positive_nongap_ge hn hp

theorem depthTwo_conductor (hm : 3 ≤ m) (hC : ∀ c, C c → c ≤ m - 2)
    (hzero : C 0) : IsConductor (depthTwoSemigroup hm hC) (2 * m) := by
  constructor
  · intro n hn hg
    have := gap_lt_twice hm hC hg
    omega
  · intro d hd
    by_cases h : 2 * m ≤ d
    · exact h
    · have hn := hd (2 * m - 1) (by omega)
      exact False.elim (hn (Or.inr ⟨0, hzero, by omega⟩))

/-- Reflection identifies the entire gapset, not merely its cardinality. -/
theorem reflected_gap_iff (hm : 3 ≤ m) (_hC : ∀ c, C c → c ≤ m - 2)
    {n : Nat} (hn : n ≤ 2 * m - 1) :
    ReflectedGap m C (2 * m - 1 - n) ↔ C n ∨ (m ≤ n ∧ n ≤ 2 * m - 2) := by
  constructor
  · rintro (⟨hpos, hsmall⟩ | ⟨c, hc, he⟩)
    · right; omega
    · left
      have : c = n := by omega
      simpa [this] using hc
  · rintro (hc | ⟨hlo, hhi⟩)
    · right; exact ⟨n, hc, by omega⟩
    · left; omega

end BuchweitzProfiles
