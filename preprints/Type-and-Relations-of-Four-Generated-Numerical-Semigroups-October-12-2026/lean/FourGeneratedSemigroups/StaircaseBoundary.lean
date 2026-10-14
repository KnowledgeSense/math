import FourGeneratedSemigroups.StaircaseAlgebra
import Mathlib.Data.Finsupp.WellFounded

noncomputable section
namespace FourGeneratedSemigroups

/-- Minimal monomials outside the staircase, including the redundant zero variable. -/
def staircaseBoundary {S : NumericalSemigroup} (G : FourGenerated S) : Set Factorization :=
  {a | a∉staircase G ∧ ∀ b,b<a → b∈staircase G}

lemma boundary_divides_eq {S : NumericalSemigroup} (G : FourGenerated S)
    {a b : Factorization} (ha : a∈staircaseBoundary G)
    (hb : b∈staircaseBoundary G) (hba : b≤a) : b=a := by
  by_contra he
  exact hb.1 (ha.2 b (lt_of_le_of_ne hba he))

lemma exists_boundary_le {S : NumericalSemigroup} (G : FourGenerated S)
    (a : Factorization) (ha : a∉staircase G) :
    ∃ b∈staircaseBoundary G,b≤a := by
  obtain ⟨b,hb,hmin⟩ := wellFounded_lt.has_min
    {b : Factorization | b≤a ∧ b∉staircase G} ⟨a,le_rfl,ha⟩
  refine ⟨b,⟨hb.2,?_⟩,hb.1⟩
  intro c hcb
  by_contra hc
  exact hmin c ⟨le_trans hcb.le hb.1,hc⟩ hcb

/-- The boundary gives actual monomial generators of the staircase ideal. -/
theorem staircaseIdeal_eq_boundary_span (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S) :
    staircaseIdeal K G=Ideal.span
      ((fun a => MvPolynomial.monomial a (1:K)) '' staircaseBoundary G) := by
  ext f
  rw [mem_staircaseIdeal_iff,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h a ha
    exact exists_boundary_le G a (h a ha)
  · intro h a ha haT
    obtain ⟨b,hb,hba⟩ := h a ha
    exact hb.1 (staircase_lower G haT hba)

/-- No boundary generator can be removed from the actual ideal generating set. -/
theorem boundary_generator_irredundant (K : Type*) [Field K]
    {S : NumericalSemigroup} (G : FourGenerated S) (a : Factorization)
    (ha : a∈staircaseBoundary G) :
    MvPolynomial.monomial a (1:K)∉Ideal.span
      ((fun b => MvPolynomial.monomial b (1:K)) '' (staircaseBoundary G \ {a})) := by
  classical
  intro h
  have hh := MvPolynomial.mem_ideal_span_monomial_image.mp h
  obtain ⟨b,hb,hba⟩ := hh a (by simp [MvPolynomial.support_monomial])
  exact hb.2 (by simp [boundary_divides_eq G ha hb.1 hba])

lemma zero_mem_staircase {S : NumericalSemigroup} (G : FourGenerated S) :
    (0 : Factorization)∈staircase G := by
  refine ⟨rfl,(criticalExponent_spec G.generators G.positive 3).1,?_,?_⟩
  · exact ⟨0,by simp,S.monoid.zero_mem⟩
  · rintro ⟨n,hn,_⟩
    have hp := G.positive 0
    simp only [map_zero,Nat.cast_zero,zero_sub] at hn
    omega

lemma boundary_nonzero {S : NumericalSemigroup} (G : FourGenerated S)
    {a : Factorization} (ha : a∈staircaseBoundary G) : a≠0 := by
  intro he
  exact ha.1 (he ▸ zero_mem_staircase G)


/-- Every boundary monomial is one variable step above a standard monomial. -/
lemma boundary_has_predecessor {S : NumericalSemigroup} (G : FourGenerated S)
    {a : Factorization} (ha : a∈staircaseBoundary G) :
    ∃ b∈staircase G,∃ i : Fin 4,b+Finsupp.single i 1=a := by
  have hn := boundary_nonzero G ha
  have hex : ∃ i,a i≠0 := by
    by_contra hh
    push Not at hh
    exact hn (Finsupp.ext hh)
  obtain ⟨i,hi⟩ := hex
  have hle : Finsupp.single i 1≤a := Finsupp.single_le_iff.mpr (by omega)
  let b := a-Finsupp.single i 1
  have he : b+Finsupp.single i 1=a := tsub_add_cancel_of_le hle
  have hba : b<a := by
    apply lt_of_le_of_ne tsub_le_self
    intro h
    have hh := congrArg (fun x : Factorization => x i) he
    simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
    have hb : b i=a i := congrArg (fun x : Factorization => x i) h
    omega
  exact ⟨b,ha.2 b hba,i,he⟩

theorem finite_staircaseBoundary {S : NumericalSemigroup} (G : FourGenerated S)
    (hf : (staircase G).Finite) : (staircaseBoundary G).Finite := by
  have hfin := Set.Finite.image2 (fun b i => b+Finsupp.single i 1) hf
    (Set.finite_univ : (Set.univ : Set (Fin 4)).Finite)
  apply hfin.subset
  intro a ha
  obtain ⟨b,hb,i,he⟩ := boundary_has_predecessor G ha
  exact ⟨b,hb,i,Set.mem_univ _,he⟩

end FourGeneratedSemigroups
