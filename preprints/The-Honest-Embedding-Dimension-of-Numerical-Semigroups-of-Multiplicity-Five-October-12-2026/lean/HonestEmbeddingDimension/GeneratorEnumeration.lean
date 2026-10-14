import HonestEmbeddingDimension.ClassificationArithmetic
import Mathlib.Data.Finset.Sort

namespace HonestEmbeddingDimension
namespace NumericalSemigroup

/-- The actual intrinsic generator count lies between two and the multiplicity. -/
theorem embeddingDimension_bounds {S : NumericalSemigroup} {m : ℕ}
    (hm : HasMultiplicity S m) (hm1 : 1 < m) :
    2 ≤ S.embeddingDimension ∧ S.embeddingDimension ≤ m := by
  refine ⟨?_, minimalGenerators_ncard_le_multiplicity hm⟩
  have ha := S.firstNonmultiple_spec m hm1
  have hane : m ≠ S.firstNonmultiple m hm1 := by
    intro hh
    rw [← hh] at ha
    exact ha.2 (dvd_refl m)
  have hsub : ({m, S.firstNonmultiple m hm1} : Set ℕ) ⊆ S.minimalGenerators := by
    intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl
    · exact minimalGenerator_of_multiplicity hm
    · exact S.firstNonmultiple_isMinimalGenerator m hm1
  have hh := Set.ncard_le_ncard hsub (finite_minimalGenerators hm)
  simpa [embeddingDimension, hane] using hh

/-- Every numerical semigroup has its canonical increasing finite generator enumeration. -/
noncomputable def orderedMinimalGenerators {S : NumericalSemigroup} {m : ℕ}
    (hm : HasMultiplicity S m) : S.OrderedMinimalGenerators S.embeddingDimension := by
  let s := (finite_minimalGenerators hm).toFinset
  have hcard : s.card = S.embeddingDimension := by
    exact (Set.ncard_eq_toFinset_card S.minimalGenerators (finite_minimalGenerators hm)).symm
  exact {
    generators := s.orderEmbOfFin hcard
    strictMono := (s.orderEmbOfFin hcard).strictMono
    range_eq := by simp [s] }

theorem multiplicity_five_embeddingDimension_cases {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) :
    S.embeddingDimension = 2 ∨ S.embeddingDimension = 3 ∨
      S.embeddingDimension = 4 ∨ S.embeddingDimension = 5 := by
  have := embeddingDimension_bounds hm (by omega)
  omega

end NumericalSemigroup

/-- The source four-generator hypotheses have exactly embedding dimension four. -/
theorem HasFourGenerators.embeddingDimension_eq {S : NumericalSemigroup} {a b c : ℕ}
    (h : HasFourGenerators S a b c) : S.embeddingDimension = 4 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have h5b : 5 ≠ b := by omega
  have h5c : 5 ≠ c := by omega
  have hac : a ≠ c := by omega
  simp [NumericalSemigroup.embeddingDimension, h.minimalGenerators_eq,
    ne_of_lt h5a, ne_of_lt hab, ne_of_lt hbc, h5b, h5c, hac]

/-- The source five-generator hypotheses have exactly embedding dimension five. -/
theorem HasFiveGenerators.embeddingDimension_eq {S : NumericalSemigroup} {a b c d : ℕ}
    (h : HasFiveGenerators S a b c d) : S.embeddingDimension = 5 := by
  have h5a := h.five_lt_a
  have hab := h.a_lt_b
  have hbc := h.b_lt_c
  have hcd := h.c_lt_d
  have h5b : 5 ≠ b := by omega
  have h5c : 5 ≠ c := by omega
  have h5d : 5 ≠ d := by omega
  have hac : a ≠ c := by omega
  have had : a ≠ d := by omega
  have hbd : b ≠ d := by omega
  simp [NumericalSemigroup.embeddingDimension, h.minimalGenerators_eq,
    ne_of_lt h5a, ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcd, h5b, h5c, h5d, hac, had, hbd]

/-- Every intrinsic four-generator semigroup admits the sorted release presentation. -/
theorem exists_four_generators_of_embeddingDimension {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (he : S.embeddingDimension = 4) :
    ∃ a b c, HasFourGenerators S a b c := by
  let G : S.OrderedMinimalGenerators 4 := he ▸ NumericalSemigroup.orderedMinimalGenerators hm
  have h0 := G.first_eq_multiplicity hm
  refine ⟨G.generators 1, G.generators 2, G.generators 3, ?_, ?_, ?_, ?_⟩
  · rw [← G.range_eq]
    ext n
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl h0
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  · simpa only [h0] using G.strictMono (by decide : (0 : Fin 4) < 1)
  · exact G.strictMono (by decide : (1 : Fin 4) < 2)
  · exact G.strictMono (by decide : (2 : Fin 4) < 3)

/-- Every intrinsic five-generator semigroup admits the sorted release presentation. -/
theorem exists_five_generators_of_embeddingDimension {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (he : S.embeddingDimension = 5) :
    ∃ a b c d, HasFiveGenerators S a b c d := by
  let G : S.OrderedMinimalGenerators 5 := he ▸ NumericalSemigroup.orderedMinimalGenerators hm
  have h0 := G.first_eq_multiplicity hm
  refine ⟨G.generators 1, G.generators 2, G.generators 3, G.generators 4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← G.range_eq]
    ext n
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl h0
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
  · simpa only [h0] using G.strictMono (by decide : (0 : Fin 5) < 1)
  · exact G.strictMono (by decide : (1 : Fin 5) < 2)
  · exact G.strictMono (by decide : (2 : Fin 5) < 3)
  · exact G.strictMono (by decide : (3 : Fin 5) < 4)

/-- In embedding dimension two, multiplicity five gives the actual coprime pair semigroup. -/
theorem exists_pair_of_embeddingDimension_two {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) (he : S.embeddingDimension = 2) :
    ∃ a, 5 < a ∧ Nat.Coprime 5 a ∧ S.monoid = generatedPair 5 a := by
  let G : S.OrderedMinimalGenerators 2 := he ▸ NumericalSemigroup.orderedMinimalGenerators hm
  have h0 := G.first_eq_multiplicity hm
  have hlt : 5 < G.generators 1 := by
    simpa only [h0] using G.strictMono (by decide : (0 : Fin 2) < 1)
  refine ⟨G.generators 1, hlt, ?_, ?_⟩
  · exact (NumericalSemigroup.minimalGenerator_coprime_five hm (G.isMinimal 1) (by omega)).symm
  · rw [generatedPair_eq_closure, ← G.generates]
    congr 1
    ext n
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl h0
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, rfl⟩

end HonestEmbeddingDimension
