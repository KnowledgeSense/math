import MainTheorems.PureOSequences.Boxes
import MainTheorems.PureOSequences.Triples
import Mathlib.Algebra.BigOperators.Intervals

namespace ResearchMain.PureOSequences

def trianglePairs (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).filter fun p => p.1 + p.2 ≤ d

noncomputable def coordinatePairs (g : Monomial 3) (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (g 0 + 1) ×ˢ Finset.range (g 1 + 1)).filter fun p =>
    p.1 + p.2 ≤ d ∧ d - p.1 - p.2 ≤ g 2

theorem boxCount_coordinates (g : Monomial 3) (d : ℕ) :
    boxCount g d = (coordinatePairs g d).card := by
  classical
  symm
  apply Finset.card_bij (fun p _ => triple p.1 p.2 (d - p.1 - p.2))
  · intro p hp
    obtain ⟨hpair, hsum, hlast⟩ := Finset.mem_filter.mp hp
    obtain ⟨h0, h1⟩ := Finset.mem_product.mp hpair
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_divisorsFinset_iff.mpr
      rw [← triple_ext g, triple_le]
      simpa only [triple_zero, triple_one, triple_two] using
        And.intro (Nat.le_of_lt_succ (Finset.mem_range.mp h0))
          (And.intro (Nat.le_of_lt_succ (Finset.mem_range.mp h1)) hlast)
    · simp only [degree_triple]
      omega
  · intro p _ q _ heq
    exact Prod.ext
      (by simpa only [triple_zero] using congrArg (fun m => m 0) heq)
      (by simpa only [triple_one] using congrArg (fun m => m 1) heq)
  · intro m hm
    obtain ⟨hmem, hdeg⟩ := Finset.mem_filter.mp hm
    have hmg := mem_divisorsFinset_iff.mp hmem
    have hsum : m 0 + m 1 + m 2 = d := by
      simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using hdeg
    have hthird : d - m 0 - m 1 = m 2 := by omega
    refine ⟨(m 0, m 1), Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hmg 0)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le (hmg 1))⟩
    · exact ⟨by omega, by simpa only [hthird] using hmg 2⟩
    · rw [hthird]
      exact triple_ext m

theorem trianglePairs_card (d : ℕ) : (trianglePairs d).card * 2 = (d + 1) * (d + 2) := by
  rw [trianglePairs, Finset.card_filter,
    Finset.sum_product _ _ (fun p : ℕ × ℕ => if p.1 + p.2 ≤ d then (1 : ℕ) else 0)]
  have hinner : ∀ x ∈ Finset.range (d + 1),
      (∑ y ∈ Finset.range (d + 1), if x + y ≤ d then (1 : ℕ) else 0) = d + 1 - x := by
    intro x hx
    have hset : (Finset.range (d + 1)).filter (fun y => x + y ≤ d) =
        Finset.range (d + 1 - x) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      omega
    rw [← Finset.card_filter, hset, Finset.card_range]
  rw [Finset.sum_congr rfl hinner]
  have hreverse : (∑ x ∈ Finset.range (d + 1), (d + 1 - x)) =
      ∑ x ∈ Finset.range (d + 1), (x + 1) := by
    calc
      _ = ∑ x ∈ Finset.range (d + 1), (d - x + 1) :=
        Finset.sum_congr rfl (fun x hx => by
          have := Finset.mem_range.mp hx
          omega)
      _ = _ := by simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun x => x + 1) (d + 1)
  rw [hreverse, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h := Finset.sum_range_id_mul_two (d + 1)
  simp only [Nat.add_sub_cancel] at h
  nlinarith

theorem coordinatePairs_subset (g : Monomial 3) (d : ℕ) :
    coordinatePairs g d ⊆ trianglePairs d := by
  intro p hp
  have hsum := (Finset.mem_filter.mp hp).2.1
  simp only [trianglePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem coordinatePairs_saturated (g : Monomial 3) (d : ℕ)
    (h0 : d ≤ g 0) (h1 : d ≤ g 1) (h2 : d ≤ g 2) :
    coordinatePairs g d = trianglePairs d := by
  apply Finset.Subset.antisymm (coordinatePairs_subset g d)
  intro p hp
  have hsum := (Finset.mem_filter.mp hp).2
  simp only [coordinatePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem boxCount_three_bound (g : Monomial 3) (d : ℕ) :
    boxCount g d * 2 ≤ (d + 1) * (d + 2) := by
  rw [boxCount_coordinates]
  exact (Nat.mul_le_mul_right 2 (Finset.card_le_card (coordinatePairs_subset g d))).trans_eq
    (trianglePairs_card d)

theorem boxCount_three_saturated (g : Monomial 3) (d : ℕ)
    (h0 : d ≤ g 0) (h1 : d ≤ g 1) (h2 : d ≤ g 2) :
    boxCount g d * 2 = (d + 1) * (d + 2) := by
  rw [boxCount_coordinates, coordinatePairs_saturated g d h0 h1 h2]
  exact trianglePairs_card d

end ResearchMain.PureOSequences
