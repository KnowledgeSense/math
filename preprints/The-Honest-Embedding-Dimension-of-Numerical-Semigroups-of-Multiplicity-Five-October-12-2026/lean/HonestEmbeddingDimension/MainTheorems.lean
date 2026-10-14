import HonestEmbeddingDimension.FullClassification

namespace HonestEmbeddingDimension
attribute [local instance] Classical.propDecidable

namespace NumericalSemigroup

theorem exists_multiplicity (S : NumericalSemigroup) : ∃ m, HasMultiplicity S m := by
  classical
  obtain ⟨c,hc⟩ := S.exists_conductor
  have hex : ∃ n : ℕ, 0<n ∧ n∈S.monoid := ⟨c+1,by omega,hc _ (by omega)⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro n hn hn0
  exact Nat.find_min' hex ⟨hn0,hn⟩

theorem exists_analytic_realization (S : NumericalSemigroup) :
    ∃ n, AnalyticallyRealizes S n := by
  obtain ⟨m,hm⟩ := S.exists_multiplicity
  exact ⟨S.embeddingDimension,analytic_realization_embeddingDimension hm⟩

/-- The least ambient dimension among all actual complex analytic realizations. -/
noncomputable def honestEmbeddingDimension (S : NumericalSemigroup) : ℕ :=
  Nat.find S.exists_analytic_realization

theorem honestEmbeddingDimension_spec (S : NumericalSemigroup) :
    HasHonestEmbeddingDimension S S.honestEmbeddingDimension :=
  ⟨Nat.find_spec S.exists_analytic_realization,
    fun _ h => Nat.find_min' S.exists_analytic_realization h⟩

theorem honestEmbeddingDimension_eq_iff (S : NumericalSemigroup) (n : ℕ) :
    S.honestEmbeddingDimension=n ↔ HasHonestEmbeddingDimension S n := by
  constructor
  · intro hn
    rw [← hn]
    exact S.honestEmbeddingDimension_spec
  · intro hn
    exact S.honestEmbeddingDimension_spec.unique hn

end NumericalSemigroup

/-- Theorem 1.1(a): the collision criterion and its explicit residue expansion. -/
theorem theorem_one_four {S : NumericalSemigroup} {a b c : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFourGenerators S a b c) :
    (S.honestEmbeddingDimension=3 ↔ firstCollision a b<c) ∧
    (S.honestEmbeddingDimension=3 ↔
      (b%5=(2*a)%5 ∧ 2*a<c) ∨
      (b%5=(3*a)%5 ∧ c%5=(4*a)%5 ∧ 3*a<c) ∨
      (b%5=(4*a)%5 ∧ c%5=(3*a)%5 ∧ a+b<c)) :=
  ⟨(S.honestEmbeddingDimension_eq_iff 3).trans (honest_dimension_three_four_collision hm h),
    (S.honestEmbeddingDimension_eq_iff 3).trans (honest_dimension_three_four_criterion hm h)⟩

/-- Theorem 1.1(b): all five generators, with the original strict inequalities. -/
theorem theorem_one_five {S : NumericalSemigroup} {a b c d : ℕ}
    (hm : HasMultiplicity S 5) (h : HasFiveGenerators S a b c d) :
    S.honestEmbeddingDimension=3 ↔
      b%5=(2*a)%5 ∧ c%5=(3*a)%5 ∧ d%5=(4*a)%5 ∧ 2*a<c ∧ a+b<d :=
  (S.honestEmbeddingDimension_eq_iff 3).trans (honest_dimension_three_five_criterion hm h)

/-- Theorem 1.2: a complete decision rule for every numerical semigroup of multiplicity five. -/
theorem theorem_two {S : NumericalSemigroup} (hm : HasMultiplicity S 5) :
    S.honestEmbeddingDimension ∈ ({2,3,4,5} : Set ℕ) ∧
    (S.embeddingDimension=2 → S.honestEmbeddingDimension=2) ∧
    (S.embeddingDimension=3 → S.honestEmbeddingDimension=3) ∧
    (∀ a b c, HasFourGenerators S a b c →
      (S.honestEmbeddingDimension=3 ↔ firstCollision a b<c) ∧
      (S.honestEmbeddingDimension=4 ↔ ¬ firstCollision a b<c)) ∧
    (∀ a b c d, HasFiveGenerators S a b c d →
      (S.honestEmbeddingDimension=5 ↔ d<2*a) ∧
      (S.honestEmbeddingDimension=3 ↔ FiveGeneratorCriterion a b c d) ∧
      (S.honestEmbeddingDimension=4 ↔ ¬ d<2*a ∧ ¬ FiveGeneratorCriterion a b c d)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rcases honest_dimension_multiplicity_five_cases hm with h | h | h | h
    all_goals simp [(S.honestEmbeddingDimension_eq_iff _).mpr h]
  · intro he
    exact (S.honestEmbeddingDimension_eq_iff 2).mpr (honest_dimension_two_of_embeddingDimension hm he)
  · intro he
    exact (S.honestEmbeddingDimension_eq_iff 3).mpr (honest_dimension_three_of_embeddingDimension hm he)
  · intro a b c h
    refine ⟨(theorem_one_four hm h).1,?_⟩
    rw [S.honestEmbeddingDimension_eq_iff, honest_dimension_four_four_iff hm h,
      four_generator_collision_iff hm h]
  · intro a b c d h
    refine ⟨(S.honestEmbeddingDimension_eq_iff 5).trans (honest_dimension_five_iff hm h),
      (S.honestEmbeddingDimension_eq_iff 3).trans (honest_dimension_three_five_criterion hm h),?_⟩
    rw [S.honestEmbeddingDimension_eq_iff, honest_dimension_four_five_iff hm h]
    have hne := five_generator_last_ne_twice_first h
    constructor
    · rintro ⟨hc,hd⟩
      exact ⟨by omega,hc⟩
    · rintro ⟨hd,hc⟩
      exact ⟨hc,by omega⟩

end HonestEmbeddingDimension
