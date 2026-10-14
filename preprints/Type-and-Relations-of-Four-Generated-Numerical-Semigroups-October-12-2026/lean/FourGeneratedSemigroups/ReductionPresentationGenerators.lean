import FourGeneratedSemigroups.ArtinianReduction
import FourGeneratedSemigroups.MinimalPresentationCardinality

noncomputable section
namespace FourGeneratedSemigroups

/-- The presentation equations together with the killed parameter. -/
def reductionPresentationFamily (K : Type*) [Field K]
    (R : Finset (Factorization × Factorization)) : R ⊕ Unit → MvPolynomial (Fin 4) K :=
  Sum.elim (presentationFamily K R) (fun _ => MvPolynomial.X 0)

/-- An n-relation congruence presentation provides exactly n+1 indexed
homogeneous generators of the actual reduction ideal. -/
theorem reductionIdeal_eq_presentationFamily_span (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S)
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation G.generators R) :
    reductionIdeal K G = Ideal.span (Set.range (reductionPresentationFamily K R)) := by
  rw [reductionPresentationFamily, Set.Sum.elim_range, Ideal.span_union,
    presentationFamily_range, ← definingIdeal_eq_presentation_span K G.generators R hR]
  simp only [Set.range_const]
  rfl

lemma reductionPresentationFamily_homogeneous (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S)
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation G.generators R)
    (r : R ⊕ Unit) :
    MvPolynomial.IsWeightedHomogeneous G.generators (reductionPresentationFamily K R r)
      (Sum.elim (fun r : R => factorizationMap G.generators r.val.1)
        (fun _ : Unit => G.generators 0) r) := by
  cases r with
  | inl r => exact presentationFamily_homogeneous K G.generators R hR r
  | inr r => exact MvPolynomial.isWeightedHomogeneous_X K G.generators 0

/-- Compare any irredundant homogeneous family for the actual reduction with
an arbitrary congruence presentation. -/
theorem reduction_irredundant_card_le_presentation_add_one
    (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)
    {ι : Type*} [Fintype ι] (f : ι → MvPolynomial (Fin 4) K) (degree : ι → ℕ)
    (hf : ∀ i, MvPolynomial.IsWeightedHomogeneous G.generators (f i) (degree i))
    (hirred : ∀ i, f i ∉ Ideal.span (f '' {j | j ≠ i}))
    (hspan : Ideal.span (Set.range f) = reductionIdeal K G)
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation G.generators R) :
    Fintype.card ι ≤ R.card + 1 := by
  have hh := homogeneous_generators_card_le G.generators
    (fun i => Nat.ne_of_gt (G.positive i)) f (reductionPresentationFamily K R)
    degree hf hirred (hspan.trans (reductionIdeal_eq_presentationFamily_span K G R hR))
  simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit] using hh

end FourGeneratedSemigroups
