import FourGeneratedSemigroups

open FourGeneratedSemigroups

example {S : NumericalSemigroup} (G : FourGenerated S) :
    S.type + 1 ≤ presentationNumber G.generators ∧
      presentationNumber G.generators ≤ 2 * S.type + 3 :=
  type_and_relations G

example {S : NumericalSemigroup} (G : FourGenerated S)
    (R : Finset (Factorization × Factorization))
    (hR : IsMinimalPresentation G.generators R) :
    S.type + 1 ≤ R.card ∧ R.card ≤ 2 * S.type + 3 :=
  minimal_presentation_type_and_relations G R hR

example (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation G.generators R) :
    definingIdeal K G.generators = Ideal.span (presentationBinomials K R) :=
  definingIdeal_eq_presentation_span K G.generators R hR
