import FourGeneratedSemigroups.DistinguishedGenerators
import FourGeneratedSemigroups.SecondaryRedundancy

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S) (K : Type*) [Field K]

noncomputable def boundaryGenerator (p : Factorization) (a : staircaseBoundary G) :
    MvPolynomial (Fin 4) K := by
  classical
  exact if a.val=topPower G then
    MvPolynomial.monomial (topPower G) 1-MvPolynomial.monomial p 1
  else MvPolynomial.monomial a.val 1

lemma span_boundaryGenerator (p : Factorization) :
    Ideal.span (Set.range (boundaryGenerator G K p))=singleBinomialIdeal K G p := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f ⟨a,rfl⟩
    by_cases ha : a.val=topPower G
    · simp only [boundaryGenerator,ite_eq_left ha]
      exact (show Ideal.span {_} ≤ _ from le_sup_right) (Ideal.subset_span rfl)
    · simp only [boundaryGenerator,ite_eq_right ha]
      exact (show Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) '' (staircaseBoundary G \ {topPower G})) ≤ _ from le_sup_left) (Ideal.subset_span ⟨a.val,⟨a.property,ha⟩,rfl⟩)
  · apply sup_le
    · rw [Ideal.span_le]
      rintro f ⟨a,ha,rfl⟩
      apply Ideal.subset_span
      exact ⟨⟨a,ha.1⟩,by simp only [boundaryGenerator,ite_eq_right (show a≠topPower G from ha.2)]⟩
    · rw [Ideal.span_le]
      rintro f rfl
      apply Ideal.subset_span
      exact ⟨⟨topPower G,top_power_mem_boundary G⟩,by simp [boundaryGenerator]⟩

lemma span_other_boundaryGenerator_le (p : Factorization) (a : staircaseBoundary G)
    (_ha : a.val≠topPower G) :
    Ideal.span (boundaryGenerator G K p '' {b | b≠a})≤omittedBoundaryIdeal G K p a.val := by
  classical
  rw [Ideal.span_le]
  rintro f ⟨b,hb,rfl⟩
  by_cases hbt : b.val=topPower G
  · simp only [boundaryGenerator,ite_eq_left hbt]
    exact (show Ideal.span {_} ≤ _ from le_sup_right) (Ideal.subset_span rfl)
  · simp only [boundaryGenerator,ite_eq_right hbt]
    apply (show Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) '' {b | b∈staircaseBoundary G ∧ b≠a.val ∧ b≠topPower G}) ≤ _ from le_sup_left)
    exact Ideal.subset_span ⟨b.val,⟨b.property,fun h => hb (Subtype.ext h),hbt⟩,rfl⟩

lemma top_boundaryGenerator_irredundant (p : Factorization) (hp : p∈staircase G)
    (a : staircaseBoundary G) (ha : a.val=topPower G) :
    boundaryGenerator G K p a∉Ideal.span (boundaryGenerator G K p '' {b | b≠a}) := by
  classical
  intro h
  have hle : Ideal.span (boundaryGenerator G K p '' {b | b≠a})≤
      Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) ''
        (staircaseBoundary G \ {topPower G})) := by
    rw [Ideal.span_le]
    rintro f ⟨b,hb,rfl⟩
    have hbt : b.val≠topPower G := fun he => hb (Subtype.ext (he.trans ha.symm))
    simp only [boundaryGenerator,ite_eq_right hbt]
    exact Ideal.subset_span ⟨b.val,⟨b.property,hbt⟩,rfl⟩
  apply distinguished_binomial_not_redundant G K p hp
  simpa [boundaryGenerator,ha] using hle h

lemma zero_boundaryGenerator_irredundant (p : Factorization) (hp2 : 0<p 2)
    (a : staircaseBoundary G) (ha : a.val=Finsupp.single 0 1) :
    boundaryGenerator G K p a∉Ideal.span (boundaryGenerator G K p '' {b | b≠a}) := by
  classical
  intro h
  have hat : a.val≠topPower G := by
    intro he
    have hh := congrArg (fun b : Factorization => b 0) (ha.symm.trans he)
    simp [topPower] at hh
  have hh := span_other_boundaryGenerator_le G K p a hat h
  apply zero_variable_not_redundant G K p hp2
  simp only [boundaryGenerator,ite_eq_right hat] at hh
  simpa only [ha] using hh

lemma redundant_boundaryGenerator_conditions (p : Factorization) (hp : p∈staircase G)
    (hp2 : 0<p 2) (a : staircaseBoundary G)
    (h : boundaryGenerator G K p a∈Ideal.span (boundaryGenerator G K p '' {b | b≠a})) :
    a.val 0=0 ∧ a.val≠topPower G ∧
      MvPolynomial.monomial a.val (1:K)∈omittedBoundaryIdeal G K p a.val := by
  classical
  have hat : a.val≠topPower G := fun he => top_boundaryGenerator_irredundant G K p hp a he h
  have ha0 : a.val 0=0 := by
    by_contra hn
    have he := boundary_positive_zero_eq G a.val a.property (Nat.pos_of_ne_zero hn)
    exact zero_boundaryGenerator_irredundant G K p hp2 a he h
  refine ⟨ha0,hat,?_⟩
  have hh := span_other_boundaryGenerator_le G K p a hat h
  simpa only [boundaryGenerator,ite_eq_right hat] using hh

theorem primary_boundaryGenerator_redundant_unique
    (hG : PrimaryOrdering G) (p : Factorization) (hpT : p∈staircase G)
    (hp3 : p 3=0) (hp1 : 0<p 1) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a b : staircaseBoundary G)
    (ha : boundaryGenerator G K p a∈Ideal.span (boundaryGenerator G K p '' {c | c≠a}))
    (hb : boundaryGenerator G K p b∈Ideal.span (boundaryGenerator G K p '' {c | c≠b})) : a=b := by
  obtain ⟨ha0,hat,hared⟩ := redundant_boundaryGenerator_conditions G K p hpT hp2 a ha
  obtain ⟨hb0,hbt,hbred⟩ := redundant_boundaryGenerator_conditions G K p hpT hp2 b hb
  apply Subtype.ext
  exact redundant_boundary_unique G K hG p hpT.1 hp3 hp1 hp2 hp hfull
    a.val b.val a.property ha0 hat b.property hb0 hbt hared hbred

theorem secondary_boundaryGenerator_redundant_unique
    (hu : ∀i j k, CriticalArc G.generators G.positive i j →
      CriticalArc G.generators G.positive i k → j=k)
    (h10 : CriticalArc G.generators G.positive 1 0)
    (p : Factorization) (hpT : p∈staircase G)
    (hp1 : p 1=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a b : staircaseBoundary G)
    (ha : boundaryGenerator G K p a∈Ideal.span (boundaryGenerator G K p '' {c | c≠a}))
    (hb : boundaryGenerator G K p b∈Ideal.span (boundaryGenerator G K p '' {c | c≠b})) : a=b := by
  obtain ⟨ha0,hat,hared⟩ := redundant_boundaryGenerator_conditions G K p hpT hp2 a ha
  obtain ⟨hb0,hbt,hbred⟩ := redundant_boundaryGenerator_conditions G K p hpT hp2 b hb
  apply Subtype.ext
  exact secondary_redundant_boundary_unique G K hu h10 p hpT.1 hp1 hp3 hp2 hp hfull
    a.val b.val a.property ha0 hat b.property hb0 hbt hared hbred

end FourGeneratedSemigroups
