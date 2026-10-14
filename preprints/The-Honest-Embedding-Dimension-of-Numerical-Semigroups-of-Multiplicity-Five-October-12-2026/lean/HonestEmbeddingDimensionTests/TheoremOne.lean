import HonestEmbeddingDimension.ThreeDimensionalClassification

open HonestEmbeddingDimension

/-- Expanded original analytic minimum: the value set uses actual analytic outer germs and their orders. -/
def ExactAnalyticMinimum (S : NumericalSemigroup) (n : ℕ) : Prop :=
  (∃ F : ℂ → Fin n → ℂ, (∀ i, AnalyticAt ℂ (fun t => F t i) 0) ∧ F 0=0 ∧
    {v : ℕ | ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G 0 ∧
      analyticOrderAt (fun t => G (F t)) 0=v} = (S.monoid : Set ℕ)) ∧
  ∀ e, (∃ F : ℂ → Fin e → ℂ, (∀ i, AnalyticAt ℂ (fun t => F t i) 0) ∧ F 0=0 ∧
    {v : ℕ | ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G 0 ∧
      analyticOrderAt (fun t => G (F t)) 0=v} = (S.monoid : Set ℕ)) → n ≤ e

example (S : NumericalSemigroup) (a b c : ℕ) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n)
    (hgens : S.minimalGenerators = {5,a,b,c}) (ha : 5<a) (hab : a<b) (hbc : b<c) :
    ExactAnalyticMinimum S 3 ↔ firstCollision a b < c := by
  exact honest_dimension_three_four_collision ⟨by decide,h5,hmin⟩ ⟨hgens,ha,hab,hbc⟩

example (S : NumericalSemigroup) (a b c : ℕ) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n)
    (hgens : S.minimalGenerators = {5,a,b,c}) (ha : 5<a) (hab : a<b) (hbc : b<c) :
    ExactAnalyticMinimum S 3 ↔
      (b%5=(2*a)%5 ∧ 2*a<c) ∨
      (b%5=(3*a)%5 ∧ c%5=(4*a)%5 ∧ 3*a<c) ∨
      (b%5=(4*a)%5 ∧ c%5=(3*a)%5 ∧ a+b<c) := by
  exact honest_dimension_three_four_criterion ⟨by decide,h5,hmin⟩ ⟨hgens,ha,hab,hbc⟩

example (S : NumericalSemigroup) (a b c d : ℕ) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n)
    (hgens : S.minimalGenerators = {5,a,b,c,d})
    (ha : 5<a) (hab : a<b) (hbc : b<c) (hcd : c<d) :
    ExactAnalyticMinimum S 3 ↔
      b%5=(2*a)%5 ∧ c%5=(3*a)%5 ∧ d%5=(4*a)%5 ∧ 2*a<c ∧ a+b<d := by
  exact honest_dimension_three_five_criterion ⟨by decide,h5,hmin⟩ ⟨hgens,ha,hab,hbc,hcd⟩

#print axioms honest_dimension_three_four_collision
#print axioms honest_dimension_three_four_criterion
#print axioms honest_dimension_three_five_criterion
