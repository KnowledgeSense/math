import HonestEmbeddingDimension

open HonestEmbeddingDimension

/-- Expanded original analytic minimum: the value set uses actual analytic outer germs and their orders. -/
def ExactAnalyticMinimumTwo (S : NumericalSemigroup) (n : ℕ) : Prop :=
  (∃ F : ℂ → Fin n → ℂ, (∀ i, AnalyticAt ℂ (fun t => F t i) 0) ∧ F 0=0 ∧
    {v : ℕ | ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G 0 ∧
      analyticOrderAt (fun t => G (F t)) 0=v} = (S.monoid : Set ℕ)) ∧
  ∀ e, (∃ F : ℂ → Fin e → ℂ, (∀ i, AnalyticAt ℂ (fun t => F t i) 0) ∧ F 0=0 ∧
    {v : ℕ | ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G 0 ∧
      analyticOrderAt (fun t => G (F t)) 0=v} = (S.monoid : Set ℕ)) → n ≤ e


example (S : NumericalSemigroup) (n : ℕ) :
    S.honestEmbeddingDimension=n ↔ ExactAnalyticMinimumTwo S n :=
  S.honestEmbeddingDimension_eq_iff n

example (S : NumericalSemigroup) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n) :
    S.honestEmbeddingDimension ∈ ({2,3,4,5} : Set ℕ) ∧
    (S.minimalGenerators.ncard=2 → S.honestEmbeddingDimension=2) ∧
    (S.minimalGenerators.ncard=3 → S.honestEmbeddingDimension=3) := by
  have h := theorem_two (⟨by decide,h5,hmin⟩ : HasMultiplicity S 5)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

example (S : NumericalSemigroup) (a b c : ℕ) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n)
    (hgens : S.minimalGenerators = {5,a,b,c}) (ha : 5<a) (hab : a<b) (hbc : b<c) :
    (S.honestEmbeddingDimension=3 ↔ firstCollision a b<c) ∧
    (S.honestEmbeddingDimension=4 ↔ ¬ firstCollision a b<c) :=
  (theorem_two ⟨by decide,h5,hmin⟩).2.2.2.1 a b c ⟨hgens,ha,hab,hbc⟩

example (S : NumericalSemigroup) (a b c d : ℕ) (h5 : 5 ∈ S.monoid)
    (hmin : ∀ n ∈ S.monoid, 0<n → 5≤n)
    (hgens : S.minimalGenerators = {5,a,b,c,d})
    (ha : 5<a) (hab : a<b) (hbc : b<c) (hcd : c<d) :
    (S.honestEmbeddingDimension=5 ↔ d<2*a) ∧
    (S.honestEmbeddingDimension=3 ↔
      b%5=(2*a)%5 ∧ c%5=(3*a)%5 ∧ d%5=(4*a)%5 ∧ 2*a<c ∧ a+b<d) ∧
    (S.honestEmbeddingDimension=4 ↔ ¬ d<2*a ∧
      ¬ (b%5=(2*a)%5 ∧ c%5=(3*a)%5 ∧ d%5=(4*a)%5 ∧ 2*a<c ∧ a+b<d)) :=
  (theorem_two ⟨by decide,h5,hmin⟩).2.2.2.2 a b c d ⟨hgens,ha,hab,hbc,hcd⟩

#print axioms NumericalSemigroup.honestEmbeddingDimension_spec
#print axioms theorem_one_four
#print axioms theorem_one_five
#print axioms theorem_two
