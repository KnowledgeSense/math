import HonestEmbeddingDimension.ThreeDimensionalClassification
import HonestEmbeddingDimension.SmallDimensions

namespace HonestEmbeddingDimension

/-- The remaining four-generator clause of Theorem 1.2. -/
theorem honest_dimension_four_four_iff {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    HasHonestEmbeddingDimension S 4 ↔ ¬ FourGeneratorCriterion a b c := by
  constructor
  · intro hdim hcrit
    have hthree := (honest_dimension_three_four_criterion hm h).mpr hcrit
    have := hdim.2 3 hthree.1
    omega
  · intro hnot
    have hreal := analytic_realization_embeddingDimension hm
    rw [h.embeddingDimension_eq] at hreal
    refine ⟨hreal,fun e he => ?_⟩
    have hlow := h.analytic_dimension_ge_three hm he
    by_contra hh
    have heq : e=3 := by omega
    subst e
    exact hnot ((honest_dimension_three_four_criterion hm h).mp
      ⟨he,fun _ hr => h.analytic_dimension_ge_three hm hr⟩)

/-- The remaining five-generator clause of Theorem 1.2. -/
theorem honest_dimension_four_five_iff {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    HasHonestEmbeddingDimension S 4 ↔
      ¬ FiveGeneratorCriterion a b c d ∧ 2*a<d := by
  constructor
  · intro hdim
    constructor
    · intro hcrit
      have hthree := (honest_dimension_three_five_criterion hm h).mpr hcrit
      have := hdim.2 3 hthree.1
      omega
    · have hne := five_generator_last_ne_twice_first h
      by_contra hn
      have hd : d<2*a := by omega
      have := five_generator_maximal_dimension_lower hm h hd hdim.1
      omega
  · rintro ⟨hnot,hd⟩
    refine ⟨analytic_realization_five_nonmaximal hm h hd,fun e he => ?_⟩
    have hlow := h.analytic_dimension_ge_three hm he
    by_contra hh
    have heq : e=3 := by omega
    subst e
    exact hnot ((honest_dimension_three_five_criterion hm h).mp
      ⟨he,fun _ hr => h.analytic_dimension_ge_three hm hr⟩)

/-- Every numerical semigroup of multiplicity five has one of the four stated
honest embedding dimensions, with the minimum taken over genuine analytic germs. -/
theorem honest_dimension_multiplicity_five_cases {S : NumericalSemigroup}
    (hm : HasMultiplicity S 5) :
    HasHonestEmbeddingDimension S 2 ∨ HasHonestEmbeddingDimension S 3 ∨
      HasHonestEmbeddingDimension S 4 ∨ HasHonestEmbeddingDimension S 5 := by
  classical
  rcases NumericalSemigroup.multiplicity_five_embeddingDimension_cases hm with he | he | he | he
  · exact Or.inl (honest_dimension_two_of_embeddingDimension hm he)
  · exact Or.inr (Or.inl (honest_dimension_three_of_embeddingDimension hm he))
  · obtain ⟨a,b,c,h⟩ := exists_four_generators_of_embeddingDimension hm he
    by_cases hc : FourGeneratorCriterion a b c
    · exact Or.inr (Or.inl ((honest_dimension_three_four_criterion hm h).mpr hc))
    · exact Or.inr (Or.inr (Or.inl ((honest_dimension_four_four_iff hm h).mpr hc)))
  · obtain ⟨a,b,c,d,h⟩ := exists_five_generators_of_embeddingDimension hm he
    by_cases hd : d<2*a
    · exact Or.inr (Or.inr (Or.inr ((honest_dimension_five_iff hm h).mpr hd)))
    · by_cases hc : FiveGeneratorCriterion a b c d
      · exact Or.inr (Or.inl ((honest_dimension_three_five_criterion hm h).mpr hc))
      · have hgt : 2*a<d := by have := five_generator_last_ne_twice_first h; omega
        exact Or.inr (Or.inr (Or.inl ((honest_dimension_four_five_iff hm h).mpr ⟨hc,hgt⟩)))

theorem HasHonestEmbeddingDimension.unique {S : NumericalSemigroup} {d e : ℕ}
    (hd : HasHonestEmbeddingDimension S d) (he : HasHonestEmbeddingDimension S e) : d=e :=
  le_antisymm (hd.2 e he.1) (he.2 d hd.1)

end HonestEmbeddingDimension
