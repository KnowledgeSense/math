import FourGeneratedSemigroups.SingleRelationMembership
import FourGeneratedSemigroups.BoundaryPresentation

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma topRelation_weight (p : Factorization)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    {a b : Factorization} (h : topRelation (criticalExponent G.generators G.positive 3) p a b) :
    factorizationMap G.generators a=factorizationMap G.generators b := by
  have hle : topRelation (criticalExponent G.generators G.positive 3) p ≤
      factorizationCongruence G.generators := by
    apply AddCon.addConGen_le.mpr
    rintro x y ⟨rfl,rfl⟩
    change factorizationMap G.generators _=factorizationMap G.generators _
    simpa using hp.symm
  exact hle h

/-- Divisibility of one plane boundary generator by another modulo the
pure-power relation forces the exceptional critical-zero degree. -/
theorem plane_boundary_relation_exceptional_with_witness (p : Factorization)
    (hp0 : p 0=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (a b r : Factorization) (ha : PlaneBoundary G a) (hb : b∈staircaseBoundary G)
    (hbt : b≠topPower G) (hba : b≠a)
    (hrel : topRelation (criticalExponent G.generators G.positive 3) p a (r+b)) :
    ∃q<criticalExponent G.generators G.positive 3,
      factorizationMap G.generators a=criticalExponent G.generators G.positive 0*G.generators 0+q*G.generators 3 ∧
      factorizationMap G.generators b=criticalExponent G.generators G.positive 0*G.generators 0 := by
  let A := criticalExponent G.generators G.positive 3
  have hA : 0<A := (criticalExponent_spec G.generators G.positive 3).1
  have hzero := topRelation_zero hp0 hrel
  have hr0 : r 0=0 := by simpa [ha.2.1] using (show (r+b) 0=0 from hzero.symm.trans ha.2.1) |> fun h => (Nat.add_eq_zero_iff.mp h).1
  have hb0 : b 0=0 := by
    have hh : r 0+b 0=0 := hzero.symm.trans ha.2.1
    omega
  obtain ⟨k,hk,hcoord⟩ := topRelation_plane hA hp3 ha.2.2.1 hrel
  have hbA := boundary_not_apery G b ((mem_threeBoundaryFinset G b).mpr ⟨hb,hb0⟩) hbt
  obtain ⟨c,hc0,hc⟩ := exists_factorization_using_zero G b hbA
  have hw : factorizationMap G.generators (c+r)=factorizationMap G.generators a := by
    have hh := topRelation_weight G p hp hrel
    simp only [map_add] at hh ⊢
    omega
  have hcr0 : 0<(c+r) 0 := by simp [hc0]
  have h1 := boundary_factorization_disjoint G a ha.1 (c+r) hw hcr0 1 (by decide) ha.2.2.2.1
  have h2 := boundary_factorization_disjoint G a ha.1 (c+r) hw hcr0 2 (by decide) ha.2.2.2.2
  have hc1 : c 1=0 := by simpa only [Finsupp.add_apply] using h1 |> fun h => (Nat.add_eq_zero_iff.mp h).1
  have hc2 : c 2=0 := by simpa only [Finsupp.add_apply] using h2 |> fun h => (Nat.add_eq_zero_iff.mp h).1
  have hr1 : r 1=0 := by have hh : c 1+r 1=0 := h1; omega
  have hr2 : r 2=0 := by have hh : c 2+r 2=0 := h2; omega
  have hb3 : 0<b 3 := by
    by_contra hn
    have hle : b≤a := by
      intro i; fin_cases i <;> change b _≤a _
      · simp [hb0,ha.2.1]
      · change b 1≤a 1
        have hh := hcoord 1 (by decide); simp only [Finsupp.add_apply,hr1,zero_add] at hh; omega
      · change b 2≤a 2
        have hh := hcoord 2 (by decide); simp only [Finsupp.add_apply,hr2,zero_add] at hh; omega
      · change b 3≤a 3
        omega
    exact hba (boundary_divides_eq G ha.1 hb hle)
  have hc3 := boundary_factorization_disjoint G b hb c hc hc0 3 (by decide) hb3
  have hcshape : c=Finsupp.single 0 (c 0) := by ext i; fin_cases i <;> simp [hc1,hc2,hc3]
  have hcweight : factorizationMap G.generators b=c 0*G.generators 0 := by rw [hcshape] at hc; simpa using hc.symm
  have hcmin := criticalExponent_le G.generators G.positive 0 (c 0) ⟨hc0,b,hb0,hcweight⟩
  have hcmax := plane_carry_zero_le G p hp0 hp2 hp a ha (c+r) hw hcr0
  have hceq : c 0=criticalExponent G.generators G.positive 0 := by simp only [Finsupp.add_apply,hr0,Nat.add_zero] at hcmax; omega
  have hrshape : r=Finsupp.single 3 (r 3) := by ext i; fin_cases i <;> simp [hr0,hr1,hr2]
  refine ⟨r 3,?_,?_⟩
  · have hh := plane_carry_third_lt G p hp0 hp2 hp a ha (c+r) hw hcr0
    simpa [hc3] using hh
  · constructor
    · rw [hcshape,hrshape] at hw
      simpa [hceq] using hw.symm
    · simpa [hceq] using hcweight


 theorem plane_boundary_relation_exceptional (p : Factorization)
    (hp0 : p 0=0) (hp3 : p 3=0) (hp2 : 0<p 2)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (a b r : Factorization) (ha : PlaneBoundary G a) (hb : b∈staircaseBoundary G)
    (hbt : b≠topPower G) (hba : b≠a)
    (hrel : topRelation (criticalExponent G.generators G.positive 3) p a (r+b)) :
    ∃q<criticalExponent G.generators G.positive 3,
      factorizationMap G.generators a=criticalExponent G.generators G.positive 0*G.generators 0+q*G.generators 3 := by
  obtain ⟨q,hq,hqa,_⟩ := plane_boundary_relation_exceptional_with_witness G p hp0 hp3 hp2 hp a b r ha hb hbt hba hrel
  exact ⟨q,hq,hqa⟩

end FourGeneratedSemigroups
