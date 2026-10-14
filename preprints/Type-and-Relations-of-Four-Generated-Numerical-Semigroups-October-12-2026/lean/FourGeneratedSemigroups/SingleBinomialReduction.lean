import FourGeneratedSemigroups.BoundaryPurePower
import FourGeneratedSemigroups.ArtinianReduction

noncomputable section
namespace FourGeneratedSemigroups
variable (K : Type*) [Field K] {S : NumericalSemigroup} (G : FourGenerated S)

/-- The cutoff pure-power exponent. -/
def topPower : Factorization := Finsupp.single 3 (criticalExponent G.generators G.positive 3)

/-- The actual boundary presentation with its cutoff pure power replaced by one binomial. -/
def singleBinomialIdeal (p : Factorization) : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) ''
    (staircaseBoundary G \ {topPower G})) ⊔
  Ideal.span {MvPolynomial.monomial (topPower G) 1-MvPolynomial.monomial p 1}

lemma cutoff_monomial_mem_singleBinomialIdeal (p a : Factorization)
    (ha : a∉staircase G) (hcut : a 3<criticalExponent G.generators G.positive 3) :
    MvPolynomial.monomial a (1:K)∈singleBinomialIdeal K G p := by
  apply (show Ideal.span ((fun b => MvPolynomial.monomial b (1:K)) ''
    (staircaseBoundary G \ {topPower G}))≤singleBinomialIdeal K G p from le_sup_left)
  rw [MvPolynomial.mem_ideal_span_monomial_image]
  intro b hb
  have hba : b=a := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst b
  obtain ⟨c,hc,hca⟩ := exists_boundary_le G a ha
  refine ⟨c,⟨hc,?_⟩,hca⟩
  intro he
  have hce : c=topPower G := Set.mem_singleton_iff.mp he
  have hh := hca 3
  simp [hce,topPower] at hh
  omega

lemma singleBinomial_step (p r : Factorization) :
    Ideal.Quotient.mk (singleBinomialIdeal K G p)
      (MvPolynomial.monomial (topPower G+r) 1)=
    Ideal.Quotient.mk (singleBinomialIdeal K G p)
      (MvPolynomial.monomial (p+r) 1) := by
  apply Ideal.Quotient.eq.mpr
  have hg : MvPolynomial.monomial (topPower G) (1:K)-MvPolynomial.monomial p 1∈
      singleBinomialIdeal K G p :=
    (show Ideal.span {MvPolynomial.monomial (topPower G) 1-MvPolynomial.monomial p 1}≤
      singleBinomialIdeal K G p from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  have hh := (singleBinomialIdeal K G p).mul_mem_right (MvPolynomial.monomial r 1) hg
  simpa only [sub_mul,MvPolynomial.monomial_mul_monomial,one_mul] using hh

/-- The single critical binomial reduces every monomial to its genuine Apéry normal form. -/
theorem singleBinomial_normal_form (p : Factorization) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) (a : Factorization) :
    (∀ b∈staircase G,factorizationMap G.generators a=factorizationMap G.generators b →
      Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial a 1)=
        Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial b 1)) ∧
    ((factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0) →
      Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial a 1)=0) := by
  have hall : ∀ n,∀ a : Factorization,a 3=n →
    (∀ b∈staircase G,factorizationMap G.generators a=factorizationMap G.generators b →
      Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial a 1)=
        Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial b 1)) ∧
    ((factorizationMap G.generators a : ℤ)∉S.apery (G.generators 0) →
      Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial a 1)=0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha3
      by_cases hcut : a 3<criticalExponent G.generators G.positive 3
      · constructor
        · intro b hb hab
          have hA : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0) := hab ▸ hb.2.2
          have haT : a∈staircase G :=
            ⟨G.factorization_coordinate_zero_of_apery 0 a hA,hcut,hA⟩
          have he := hinj haT hb (congrArg (fun n : ℕ => (n : ℤ)) hab)
          rw [he]
        · intro hnA
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          exact cutoff_monomial_mem_singleBinomialIdeal K G p a (fun h => hnA h.2.2) hcut
      · have hle : topPower G≤a := Finsupp.single_le_iff.mpr (Nat.le_of_not_gt hcut)
        obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
        have hsmall : (p+r) 3<n := by
          have hh : a 3=criticalExponent G.generators G.positive 3+r 3 := by simp [hr,topPower]
          have hpos := (criticalExponent_spec G.generators G.positive 3).1
          simp only [Finsupp.add_apply,hp3,zero_add]
          omega
        have hw : factorizationMap G.generators (p+r)=factorizationMap G.generators a := by
          simp [hr,topPower,hp]
        have hrec := ih ((p+r) 3) hsmall (p+r) rfl
        have he : Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial a 1)=
            Ideal.Quotient.mk (singleBinomialIdeal K G p) (MvPolynomial.monomial (p+r) 1) := by
          rw [hr]; exact singleBinomial_step K G p r
        constructor
        · intro b hb hab
          exact he.trans (hrec.1 b hb (hw.trans hab))
        · intro hnA
          exact he.trans (hrec.2 (by simpa only [hw] using hnA))
  exact hall (a 3) a rfl


/-- Replacing the cutoff boundary power by its actual critical binomial gives
exactly the defining ideal of the Artinian reduction. -/
theorem reductionIdeal_eq_singleBinomialIdeal (p : Factorization) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=
      criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G)) :
    reductionIdeal K G=singleBinomialIdeal K G p := by
  apply le_antisymm
  · apply sup_le
    · rw [definingIdeal_eq_binomial_span,Ideal.span_le]
      rintro f ⟨a,b,hab,rfl⟩
      apply Ideal.Quotient.eq.mp
      have hna := singleBinomial_normal_form K G p hp3 hp hinj a
      have hnb := singleBinomial_normal_form K G p hp3 hp hinj b
      by_cases ha : (factorizationMap G.generators a : ℤ)∈S.apery (G.generators 0)
      · obtain ⟨c,hc,hc0,hc3⟩ := apery_has_bounded_factorization G _ ha
        have hcT : c∈staircase G := ⟨hc0,hc3,by simpa only [hc] using ha⟩
        have hw : factorizationMap G.generators c=factorizationMap G.generators a :=
          Int.ofNat_inj.mp hc
        exact (hna.1 c hcT hw.symm).trans (hnb.1 c hcT (hab.symm.trans hw.symm)).symm
      · exact (hna.2 ha).trans (hnb.2 (by simpa only [hab] using ha)).symm
    · rw [Ideal.span_le,Set.singleton_subset_iff]
      change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
      apply cutoff_monomial_mem_singleBinomialIdeal K G p
      · intro h
        have hh := h.1
        simp at hh
      · simpa using (criticalExponent_spec G.generators G.positive 3).1
  · apply sup_le
    · rw [Ideal.span_le]
      rintro f ⟨a,ha,rfl⟩
      have hcut := boundary_below_top_unless_pure G a ha.1
        (fun he => ha.2 (Set.mem_singleton_iff.mpr he))
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply reduction_monomial_zero_of_not_apery K G a
      intro hA
      exact ha.1.1 ⟨G.factorization_coordinate_zero_of_apery 0 a hA,hcut,hA⟩
    · rw [Ideal.span_le,Set.singleton_subset_iff]
      apply (show definingIdeal K G.generators≤reductionIdeal K G from le_sup_left)
      apply (binomial_mem_definingIdeal_iff K G.generators _ _).mpr
      simpa [topPower] using hp.symm

/-- The normal form of an Apéry critical degree involves no third variable. -/
theorem critical_apery_representative_third_zero
    (ha : ((criticalExponent G.generators G.positive 3*G.generators 3 : ℕ) : ℤ)∈
      S.apery (G.generators 0)) :
    (aperyRepresentative G ⟨criticalExponent G.generators G.positive 3*G.generators 3,ha⟩) 3=0 := by
  let n : AperyDegree G := ⟨criticalExponent G.generators G.positive 3*G.generators 3,ha⟩
  have hw := aperyRepresentative_weight G n
  rcases critical_factorization_dichotomy G.generators G.positive 3
    (aperyRepresentative G n) hw with hp|hp
  · have hmem := aperyRepresentative_mem G n
    have hh := hmem.2.1
    rw [hp] at hh
    simp at hh
  · exact hp

end FourGeneratedSemigroups
