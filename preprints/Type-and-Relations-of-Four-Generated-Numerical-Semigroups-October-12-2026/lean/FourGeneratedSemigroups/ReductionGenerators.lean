import FourGeneratedSemigroups.LowerBoundSetup
import FourGeneratedSemigroups.HomogeneousGeneratorComparison

noncomputable section
namespace FourGeneratedSemigroups

lemma weight_eq_factorizationMap (d : Fin 4→ℕ) (a : Factorization) :
    Finsupp.weight d a=factorizationMap d a := by
  rw [Finsupp.weight_apply,Finsupp.sum_fintype]
  · rfl
  · simp

lemma monomial_weighted_homogeneous (K : Type*) [Field K] (d : Fin 4→ℕ) (a : Factorization) :
    MvPolynomial.IsWeightedHomogeneous d (MvPolynomial.monomial a (1:K))
      (factorizationMap d a) :=
  MvPolynomial.isWeightedHomogeneous_monomial d a 1 (weight_eq_factorizationMap d a)

lemma boundaryGenerator_homogeneous {S : NumericalSemigroup} (G : FourGenerated S)
    (K : Type*) [Field K] (p : Factorization)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (a : staircaseBoundary G) :
    MvPolynomial.IsWeightedHomogeneous G.generators (boundaryGenerator G K p a)
      (factorizationMap G.generators a.val) := by
  classical
  by_cases ha : a.val=topPower G
  · simp only [boundaryGenerator,ite_eq_left ha]
    apply MvPolynomial.IsWeightedHomogeneous.sub
    · simpa only [ha] using monomial_weighted_homogeneous K G.generators (topPower G)
    · convert monomial_weighted_homogeneous K G.generators p using 1
      simp [ha,topPower,hp]
  · simp only [boundaryGenerator,ite_eq_right ha]
    exact monomial_weighted_homogeneous K G.generators a.val

def reductionPresentationGenerator (K : Type*) [Field K]
    (R : Finset (Factorization×Factorization)) : Option R→MvPolynomial (Fin 4) K
  | none => MvPolynomial.X 0
  | some r => MvPolynomial.monomial r.val.1 1-MvPolynomial.monomial r.val.2 1

lemma span_reductionPresentationGenerator {S : NumericalSemigroup} (G : FourGenerated S)
    (K : Type*) [Field K] (R : Finset (Factorization×Factorization))
    (hR : IsPresentation G.generators R) :
    Ideal.span (Set.range (reductionPresentationGenerator K R))=reductionIdeal K G := by
  rw [reductionIdeal,definingIdeal_eq_presentation_span K G.generators R hR]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f ⟨r,rfl⟩
    cases r with
    | none => exact (show Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 4) K)} ≤ _ from le_sup_right) (Ideal.subset_span rfl)
    | some r =>
        exact (show Ideal.span (presentationBinomials K R) ≤ _ from le_sup_left)
          (Ideal.subset_span ⟨r.val,r.property,rfl⟩)
  · apply sup_le
    · rw [Ideal.span_le]
      rintro f ⟨r,hr,rfl⟩
      exact Ideal.subset_span ⟨some ⟨r,hr⟩,rfl⟩
    · rw [Ideal.span_le]
      rintro f rfl
      exact Ideal.subset_span ⟨none,rfl⟩

end FourGeneratedSemigroups
