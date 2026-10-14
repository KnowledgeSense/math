import FourGeneratedSemigroups.ExceptionalBoundary

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

/-- The ideal obtained by omitting one boundary monomial from the distinguished
binomial presentation. -/
def omittedBoundaryIdeal (K : Type*) [Field K] (p a : Factorization) :
    Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) ''
    {b | b∈staircaseBoundary G ∧ b≠a ∧ b≠topPower G}) ⊔
  Ideal.span {MvPolynomial.monomial (topPower G) 1-MvPolynomial.monomial p 1}

lemma redundant_boundary_ge_replacement (K : Type*) [Field K] (p a : Factorization)
    (ha : a∈staircaseBoundary G) (hat : a≠topPower G)
    (h : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a) : p≤a := by
  classical
  let B : Set Factorization := {b | b∈staircaseBoundary G ∧ b≠a ∧ b≠topPower G}
  let D := B∪{topPower G,p}
  let J : Ideal (MvPolynomial (Fin 4) K) :=
    Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) '' D)
  have hle : omittedBoundaryIdeal G K p a≤J := by
    apply sup_le
    · apply Ideal.span_mono
      rintro f ⟨b,hb,rfl⟩
      exact ⟨b,Or.inl hb,rfl⟩
    · rw [Ideal.span_le]
      rintro f rfl
      apply Ideal.sub_mem
      · exact Ideal.subset_span ⟨topPower G,Or.inr (by simp),rfl⟩
      · exact Ideal.subset_span ⟨p,Or.inr (by simp),rfl⟩
  obtain ⟨b,hb,hba⟩ := (MvPolynomial.mem_ideal_span_monomial_image.mp (hle h)) a (by simp)
  rcases hb with hb|hb
  · exact (hb.2.1 (boundary_divides_eq G ha hb.1 hba)).elim
  · rcases hb with hb|hb
    · have he : topPower G=a := boundary_divides_eq G ha (top_power_mem_boundary G) (by simpa [Set.mem_singleton_iff.mp hb] using hba)
      exact (hat he.symm).elim
    · simpa [Set.mem_singleton_iff.mp hb] using hba

/-- In a primary ordering with no full-support boundary generator, every
redundant boundary monomial has the exceptional critical-zero degree. -/
theorem redundant_boundary_exceptional (K : Type*) [Field K]
    (p : Factorization) (hp0 : p 0=0) (hp3 : p 3=0) (hp1 : 0<p 1) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a : Factorization) (ha : a∈staircaseBoundary G) (ha0 : a 0=0) (hat : a≠topPower G)
    (h : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a) :
    PlaneBoundary G a ∧ ∃q<criticalExponent G.generators G.positive 3,
      factorizationMap G.generators a=criticalExponent G.generators G.positive 0*G.generators 0+q*G.generators 3 := by
  have hpa := redundant_boundary_ge_replacement G K p a ha hat h
  have ha1 : 0<a 1 := lt_of_lt_of_le hp1 (hpa 1)
  have ha2 : 0<a 2 := lt_of_lt_of_le hp2 (hpa 2)
  have ha3 : a 3=0 := by
    by_contra hn
    apply hfull a
    refine ⟨ha,ha0,?_⟩
    intro i hi
    fin_cases i <;> simp_all ; omega
  have hplane : PlaneBoundary G a := ⟨ha,ha0,ha3,ha1,ha2⟩
  refine ⟨hplane,?_⟩
  obtain ⟨b,hb,r,hr⟩ := monomial_mem_singleRelation_implies K
    (criticalExponent G.generators G.positive 3) p a
    {b | b∈staircaseBoundary G ∧ b≠a ∧ b≠topPower G} h
  exact plane_boundary_relation_exceptional G p hp0 hp3 hp2 hp a b r hplane hb.1 hb.2.2 hb.2.1 hr

theorem redundant_boundary_unique (K : Type*) [Field K] (hG : PrimaryOrdering G)
    (p : Factorization) (hp0 : p 0=0) (hp3 : p 3=0) (hp1 : 0<p 1) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a b : Factorization) (ha : a∈staircaseBoundary G) (ha0 : a 0=0) (hat : a≠topPower G)
    (hb : b∈staircaseBoundary G) (hb0 : b 0=0) (hbt : b≠topPower G)
    (hared : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a)
    (hbred : MvPolynomial.monomial b (1:K)∈omittedBoundaryIdeal G K p b) : a=b := by
  obtain ⟨hap,q,hq,hwa⟩ := redundant_boundary_exceptional G K p hp0 hp3 hp1 hp2 hp hfull a ha ha0 hat hared
  obtain ⟨hbp,r,hr,hwb⟩ := redundant_boundary_exceptional G K p hp0 hp3 hp1 hp2 hp hfull b hb hb0 hbt hbred
  exact exceptional_plane_boundary_unique G hG a b hap hbp q r hq hr hwa hwb

end FourGeneratedSemigroups
