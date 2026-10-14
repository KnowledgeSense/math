import MeanMaximumForests.CoefficientExtensions
import MeanMaximumForests.GraphPeaks

namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A maximum independent set in the extension graph can be adjoined to the current set. -/
theorem extensions_independence_bound (s J : Finset V) (hJs : J ⊆ s) (hJi : Independent G J) :
    independenceNumber G (extensions G s J) + J.card ≤ independenceNumber G s := by
  classical
  obtain ⟨K, hK, hKi, hKc⟩ := exists_maximum_independentSet G (extensions G s J)
  have hs : extensions G s J ⊆ s := fun _ hv => ((mem_extensions G).mp hv).1
  have he : Separated G J (extensions G s J) := by
    intro u hu v hv hadj
    exact ((mem_extensions G).mp hv).2.2 u hu hadj.symm
  have hd : Disjoint J K := by
    apply disjoint_left.mpr
    intro v hvJ hvK
    exact ((mem_extensions G).mp (hK hvK)).2.1 hvJ
  have hI := (independent_union G he (Subset.refl J) hK).mpr ⟨hJi, hKi⟩
  have hc := independent_card_le G s (union_subset hJs (hK.trans hs)) hI
  rw [card_union_of_disjoint hd, hKc] at hc
  omega

/-- Bipartiteness, proved from the forest recursion, bounds each extension set. -/
theorem extensions_card_upper (hG : G.IsAcyclic) (s J : Finset V)
    (hJs : J ⊆ s) (hJi : Independent G J) :
    (extensions G s J).card ≤ 2 * (independenceNumber G s - J.card) := by
  have h₁ := forest_card_le_twice_independenceNumber G hG (extensions G s J)
  have h₂ := extensions_independence_bound G s J hJs hJi
  omega

/-- The upper coefficient-ratio inequality, proved for every finite subset of a forest. -/
theorem coefficient_extension_upper (hG : G.IsAcyclic) (s : Finset V) (k : ℕ) :
    (k + 1) * independentSetCoefficient G s (k + 1) ≤
      2 * (independenceNumber G s - k) * independentSetCoefficient G s k := by
  classical
  rw [coefficient_extension_identity]
  calc
    _ ≤ ∑ _J ∈ independentSetsOfSize G s k, 2 * (independenceNumber G s - k) := by
      apply sum_le_sum
      intro J hJ
      obtain ⟨hJs, hJi, hJk⟩ := (mem_independentSetsOfSize G).mp hJ
      simpa only [hJk] using extensions_card_upper G hG s J hJs hJi
    _ = _ := by simp [independentSetsOfSize, independentSetCoefficient, Nat.mul_comm]

omit [DecidableEq V] in
/-- Every singleton is independent, so the linear coefficient equals the number of vertices. -/
theorem coefficient_one (s : Finset V) : independentSetCoefficient G s 1 = s.card := by
  classical
  have he : (independentSetsWithin G s).filter (fun J => J.card = 1) = s.powersetCard 1 := by
    ext J
    simp only [mem_filter, mem_independentSetsWithin, mem_powersetCard]
    constructor
    · rintro ⟨⟨hJs, _⟩, hJc⟩
      exact ⟨hJs, hJc⟩
    · rintro ⟨hJs, hJc⟩
      refine ⟨⟨hJs, ?_⟩, hJc⟩
      obtain ⟨v, rfl⟩ := card_eq_one.mp hJc
      simp [Independent]
  simp only [independentSetCoefficient, he, card_powersetCard, Nat.choose_one_right]

/-- A weak peak in a graph of order at least two cannot be at the constant coefficient. -/
theorem weakLocalPeak_pos [Fintype V] {k : ℕ} (hn : 2 ≤ Fintype.card V)
    (hk : WeakLocalPeak G k) : 0 < k := by
  by_contra h
  have he : k = 0 := by omega
  have h := hk.2.2
  rw [he] at h
  simp only [Nat.zero_add, coefficient_one, coefficient_zero, card_univ] at h
  omega

/-- Every weak local peak of a forest satisfies the exact upper-end inequality. -/
theorem weakLocalPeak_upper [Fintype V] (hG : G.IsAcyclic) {k : ℕ}
    (hk : WeakLocalPeak G k) : 3 * k ≤ 2 * G.indepNum + 2 := by
  by_cases hk0 : k = 0
  · omega
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkp : k - 1 + 1 = k := by omega
    have hpos : 0 < independentSetCoefficient G univ (k - 1) := by
      apply (coefficient_pos_iff_le G univ (k - 1)).mpr
      rw [independenceNumber_univ]
      exact (Nat.sub_le k 1).trans hk.1
    have hup := coefficient_extension_upper G hG univ (k - 1)
    rw [hkp, independenceNumber_univ] at hup
    have hleft := hk.2.1.resolve_left hk0
    have hh := (Nat.mul_le_mul_left k hleft).trans hup
    have hc := Nat.le_of_mul_le_mul_right hh hpos
    have hka := hk.1
    omega

/-- The endpoint convention is immaterial for forests with at least five vertices. -/
theorem weakLocalPeak_interior [Fintype V] (hG : G.IsAcyclic)
    (hn : 5 ≤ Fintype.card V) {k : ℕ} (hk : WeakLocalPeak G k) :
    1 ≤ k ∧ k < G.indepNum := by
  have hpos := weakLocalPeak_pos G (by omega) hk
  have hupper := weakLocalPeak_upper G hG hk
  have horder := forest_card_le_twice_indepNum G hG
  have hka := hk.1
  omega

end MeanMaximumForests
