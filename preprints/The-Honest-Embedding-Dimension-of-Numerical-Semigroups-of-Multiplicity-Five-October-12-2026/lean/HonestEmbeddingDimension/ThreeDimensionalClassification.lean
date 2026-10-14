import HonestEmbeddingDimension.GeometricReleaseCases
import HonestEmbeddingDimension.BinomialReleaseCases
import HonestEmbeddingDimension.FiveGeneratorNecessity

namespace HonestEmbeddingDimension

/-- Theorem 1.1(a), in its original first-collision formulation. -/
theorem honest_dimension_three_four_collision {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    HasHonestEmbeddingDimension S 3 ↔ firstCollision a b < c := by
  constructor
  · intro hd
    exact four_generator_collision_necessary hm h hd.1
  · intro hc
    have hcases := (four_generator_realization_cases_iff hm h).mp hc
    have hreal : AnalyticallyRealizes S 3 := by
      rcases hcases with ⟨hb,hc,hgt⟩ | ⟨hb,hc,hgt⟩ | ⟨hb,hc,hgt⟩ | ⟨hb,hc,hgt⟩
      · exact analytic_realization_case_4A hm h hb hc hgt
      · exact analytic_realization_case_4B hm h hb hc hgt
      · exact analytic_realization_case_4C hm h hb hc hgt
      · exact analytic_realization_case_4D hm h hb hc hgt
    exact ⟨hreal,fun _ he => h.analytic_dimension_ge_three hm he⟩

/-- Theorem 1.1(a), with all three explicit residue alternatives. -/
theorem honest_dimension_three_four_criterion {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    HasHonestEmbeddingDimension S 3 ↔ FourGeneratorCriterion a b c :=
  (honest_dimension_three_four_collision hm h).trans (four_generator_collision_iff hm h)

/-- Theorem 1.1(b), with the original progression and strict inequalities. -/
theorem honest_dimension_three_five_criterion {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    HasHonestEmbeddingDimension S 3 ↔ FiveGeneratorCriterion a b c d := by
  constructor
  · intro hd
    exact (five_generator_criterion_iff_bounds hm h).mpr (five_generator_bounds_necessary hm h hd.1)
  · rintro ⟨hb,hc,hd,hcgt,hdgt⟩
    exact ⟨analytic_realization_five_positive hm h hb hc hd hcgt hdgt,
      fun _ he => h.analytic_dimension_ge_three hm he⟩

end HonestEmbeddingDimension
