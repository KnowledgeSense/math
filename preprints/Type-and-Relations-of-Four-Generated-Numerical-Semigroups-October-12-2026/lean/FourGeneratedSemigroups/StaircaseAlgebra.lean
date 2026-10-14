import FourGeneratedSemigroups.StaircaseCorners
import FourGeneratedSemigroups.MonomialQuotient

noncomputable section
namespace FourGeneratedSemigroups

/-- The actual monomial ideal whose standard monomials are the staircase.
The redundant variable indexed by zero lies in this ideal. -/
def staircaseIdeal (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S) :
    Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span ((fun a => MvPolynomial.monomial a (1:K)) '' (staircase G)ᶜ)

theorem mem_staircaseIdeal_iff (K : Type*) [Field K] {S : NumericalSemigroup}
    (G : FourGenerated S) (f : MvPolynomial (Fin 4) K) :
    f∈staircaseIdeal K G ↔ ∀ a∈f.support,a∉staircase G := by
  rw [staircaseIdeal,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h a ha haT
    obtain ⟨b,hb,hba⟩ := h a ha
    exact hb (staircase_lower G haT hba)
  · intro h a ha
    exact ⟨a,h a ha,le_rfl⟩

/-- A basis of the actual staircase quotient, indexed by its actual exponents. -/
noncomputable def staircaseQuotientBasis (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S) :
    Module.Basis (staircase G) K (MvPolynomial (Fin 4) K ⧸ staircaseIdeal K G) := by
  simpa only [compl_compl] using
    standardMonomialBasis (staircaseIdeal K G) (staircase G)ᶜ
      (mem_staircaseIdeal_iff K G)

theorem finrank_staircaseQuotient (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S) (hfinite : (staircase G).Finite) :
    Module.finrank K (MvPolynomial (Fin 4) K ⧸ staircaseIdeal K G)=Nat.card (staircase G) := by
  let := hfinite.fintype
  simpa using Module.finrank_eq_card_basis (staircaseQuotientBasis K G)

theorem zero_variable_mem_staircaseIdeal (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S) :
    MvPolynomial.X 0∈staircaseIdeal K G := by
  apply Ideal.subset_span
  refine ⟨Finsupp.single 0 1,?_,?_⟩
  · intro h
    have hh := h.1
    simp at hh
  · rfl

end FourGeneratedSemigroups
