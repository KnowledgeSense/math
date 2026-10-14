import FourGeneratedSemigroups.BoundaryRedundancy
import FourGeneratedSemigroups.CriticalGraphClassification

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma pureReplacement_redundant_third_zero (K : Type*) [Field K]
    (p : Factorization) (hp0 : p 0=0) (hp1 : p 1=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a : Factorization) (ha : a∈staircaseBoundary G) (ha0 : a 0=0) (hat : a≠topPower G)
    (h : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a) : a 3=0 := by
  by_contra hn
  have ha3 : 0<a 3 := Nat.pos_of_ne_zero hn
  have hpa := redundant_boundary_ge_replacement G K p a ha hat h
  have ha2 : 0<a 2 := lt_of_lt_of_le hp2 (hpa 2)
  have ha1 : a 1=0 := by
    by_contra hn1
    apply hfull a
    refine ⟨ha,ha0,?_⟩
    intro i hi
    fin_cases i <;> simp_all ; omega
  obtain ⟨b,hb,r,hr⟩ := monomial_mem_singleRelation_implies K
    (criticalExponent G.generators G.positive 3) p a
    {b | b∈staircaseBoundary G ∧ b≠a ∧ b≠topPower G} h
  have hA := (criticalExponent_spec G.generators G.positive 3).1
  have hz := topRelation_zero hp0 hr
  have hr0 : r 0=0 := by have hh : r 0+b 0=0 := hz.symm.trans ha0; omega
  have hb0 : b 0=0 := by have hh : r 0+b 0=0 := hz.symm.trans ha0; omega
  have h1 := topRelation_balance hp3 hr 1 (by decide)
  simp only [ha1,hp1,Nat.mul_zero,zero_add] at h1
  have hr1 : r 1=0 := by
    have hh : (r+b) 1=0 := by nlinarith
    have hh' : r 1+b 1=0 := hh
    omega
  obtain ⟨c,hc0,hc⟩ := exists_factorization_using_zero G b
    (boundary_not_apery G b ((mem_threeBoundaryFinset G b).mpr ⟨hb.1,hb0⟩) hb.2.2)
  have hw : factorizationMap G.generators (c+r)=factorizationMap G.generators a := by
    have hh := topRelation_weight G p hp hr
    simp only [map_add] at hh ⊢
    omega
  have hcr0 : 0<(c+r) 0 := by simp [hc0]
  have h2 := boundary_factorization_disjoint G a ha (c+r) hw hcr0 2 (by decide) ha2
  have h3 := boundary_factorization_disjoint G a ha (c+r) hw hcr0 3 (by decide) ha3
  have hr2 : r 2=0 := by have hh : c 2+r 2=0 := h2; omega
  have hr3 : r 3=0 := by have hh : c 3+r 3=0 := h3; omega
  have hrzero : r=0 := by ext i; fin_cases i <;> simp [hr0,hr1,hr2,hr3]
  rw [hrzero,zero_add] at hr
  exact hb.2.1 (topRelation_cut_injective hA hp3
    (boundary_below_top_unless_pure G a ha hat)
    (boundary_below_top_unless_pure G b hb.1 hb.2.2) hr).symm

/-- In the secondary ordering, a redundant boundary monomial must be the pure
second-variable boundary. In particular there can be at most one. -/
theorem secondary_redundant_boundary_pure (K : Type*) [Field K]
    (hu : ∀i j k, CriticalArc G.generators G.positive i j →
      CriticalArc G.generators G.positive i k → j=k)
    (h10 : CriticalArc G.generators G.positive 1 0)
    (p : Factorization) (hp0 : p 0=0) (hp1 : p 1=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a : Factorization) (ha : a∈staircaseBoundary G) (ha0 : a 0=0) (hat : a≠topPower G)
    (h : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a) :
    a=Finsupp.single 2 (a 2) := by
  have ha3 := pureReplacement_redundant_third_zero G K p hp0 hp1 hp3 hp2 hp hfull a ha ha0 hat h
  have hpa := redundant_boundary_ge_replacement G K p a ha hat h
  have ha2 : 0<a 2 := lt_of_lt_of_le hp2 (hpa 2)
  have ha1 : a 1=0 := by
    by_contra hn
    have hplane : PlaneBoundary G a := ⟨ha,ha0,ha3,Nat.pos_of_ne_zero hn,ha2⟩
    obtain ⟨b,hb,r,hr⟩ := monomial_mem_singleRelation_implies K
      (criticalExponent G.generators G.positive 3) p a
      {b | b∈staircaseBoundary G ∧ b≠a ∧ b≠topPower G} h
    obtain ⟨q,hq,hqa,hbw⟩ := plane_boundary_relation_exceptional_with_witness G
      p hp0 hp3 hp2 hp a b r hplane hb.1 hb.2.2 hb.2.1 hr
    have h01 := criticalArc_reverse_of_unique G.generators G.positive hu h10
    have hf := (critical_fiber_eq_pair G.generators G.positive hu h01 b).mp hbw
    have hz := topRelation_zero hp0 hr
    have hb0 : b 0=0 := by have hh : r 0+b 0=0 := hz.symm.trans ha0; omega
    rcases hf with hf|hf
    · have hh := congrArg (fun c : Factorization => c 0) hf
      have hpzero := (criticalExponent_spec G.generators G.positive 0).1
      simp only [Finsupp.single_eq_same,hb0] at hh
      omega
    · have hbound : a 1<criticalExponent G.generators G.positive 1 := by
        apply boundary_axis_bound G a ha 1 2 (by decide) ha2
        intro hh
        exact (criticalDegree_not_apery_iff_arc G 1 (by decide)).mpr h10 (by simpa using hh.2.2)
      have hbal := topRelation_balance hp3 hr 1 (by decide)
      simp only [hp1,Nat.zero_mul,Nat.add_zero] at hbal
      have hA := (criticalExponent_spec G.generators G.positive 3).1
      have he := Nat.eq_of_mul_eq_mul_left hA hbal
      have he' : a 1=r 1+criticalExponent G.generators G.positive 1 := by simpa [hf] using he
      omega
  ext i
  fin_cases i <;> simp [ha0,ha1,ha3]

theorem secondary_redundant_boundary_unique (K : Type*) [Field K]
    (hu : ∀i j k, CriticalArc G.generators G.positive i j →
      CriticalArc G.generators G.positive i k → j=k)
    (h10 : CriticalArc G.generators G.positive 1 0)
    (p : Factorization) (hp0 : p 0=0) (hp1 : p 1=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hfull : ∀b, ¬FullSupportBoundary G b)
    (a b : Factorization) (ha : a∈staircaseBoundary G) (ha0 : a 0=0) (hat : a≠topPower G)
    (hb : b∈staircaseBoundary G) (hb0 : b 0=0) (hbt : b≠topPower G)
    (hared : MvPolynomial.monomial a (1:K)∈omittedBoundaryIdeal G K p a)
    (hbred : MvPolynomial.monomial b (1:K)∈omittedBoundaryIdeal G K p b) : a=b := by
  have hae := secondary_redundant_boundary_pure G K hu h10 p hp0 hp1 hp3 hp2 hp hfull a ha ha0 hat hared
  have hbe := secondary_redundant_boundary_pure G K hu h10 p hp0 hp1 hp3 hp2 hp hfull b hb hb0 hbt hbred
  rcases le_total (a 2) (b 2) with hab|hba
  · apply boundary_divides_eq G hb ha
    rw [hae,hbe]
    exact Finsupp.single_le_single.mpr hab
  · symm
    apply boundary_divides_eq G ha hb
    rw [hae,hbe]
    exact Finsupp.single_le_single.mpr hba

end FourGeneratedSemigroups
