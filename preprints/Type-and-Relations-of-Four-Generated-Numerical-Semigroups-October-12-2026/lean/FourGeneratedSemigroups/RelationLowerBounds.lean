import FourGeneratedSemigroups.ReductionGenerators
import FourGeneratedSemigroups.MonomialReduction

noncomputable section
namespace FourGeneratedSemigroups
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma presentation_card_ge_boundary_sub_one (p : Factorization) (hp3 : p 3=0)
    (hp : factorizationMap G.generators p=criticalExponent G.generators G.positive 3*G.generators 3)
    (hinj : Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ)) (staircase G))
    (hunique : ∀a b : staircaseBoundary G,
      boundaryGenerator G ℚ p a∈Ideal.span (boundaryGenerator G ℚ p '' {c | c≠a}) →
      boundaryGenerator G ℚ p b∈Ideal.span (boundaryGenerator G ℚ p '' {c | c≠b}) → a=b)
    (R : Finset (Factorization×Factorization)) (hR : IsPresentation G.generators R) :
    staircaseGeneratorNumber G≤R.card+1 := by
  classical
  let : Fintype (staircaseBoundary G) := (finite_staircaseBoundary G (finite_staircase G)).fintype
  obtain ⟨T,hT,hirred,hcard⟩ := exists_large_irredundant_generator_subfamily
    (boundaryGenerator G ℚ p) hunique
  have hle := homogeneous_generators_card_le G.generators (fun i => (G.positive i).ne')
    (fun a : T => boundaryGenerator G ℚ p a.val) (reductionPresentationGenerator ℚ R)
    (fun a : T => factorizationMap G.generators a.val.val)
    (fun a => boundaryGenerator_homogeneous G ℚ p hp a.val)
    (irredundant_subfamily (boundaryGenerator G ℚ p) T hirred)
    (show Ideal.span (Set.range (fun a : T => boundaryGenerator G ℚ p a.val))=
      Ideal.span (Set.range (reductionPresentationGenerator ℚ R)) from by
      rw [span_subfamily_range,hT,span_boundaryGenerator,
        ← reductionIdeal_eq_singleBinomialIdeal ℚ G p hp3 hp hinj,
        span_reductionPresentationGenerator G ℚ R hR])
  simp only [Fintype.card_coe,Fintype.card_option] at hle
  have hboundary := boundary_card_eq_generatorNumber_add_one G
  rw [Nat.card_eq_fintype_card] at hboundary
  omega

lemma presentation_card_ge_boundary_monomial (hG : PrimaryOrdering G)
    (h30 : CriticalArc G.generators G.positive 3 0)
    (R : Finset (Factorization×Factorization)) (hR : IsPresentation G.generators R) :
    staircaseGeneratorNumber G≤R.card := by
  classical
  let : Fintype (staircaseBoundary G) := (finite_staircaseBoundary G (finite_staircase G)).fintype
  let f : staircaseBoundary G→MvPolynomial (Fin 4) ℚ := fun a => MvPolynomial.monomial a.val 1
  have hirred : ∀a, f a∉Ideal.span (f '' {b | b≠a}) := by
    intro a h
    apply boundary_generator_irredundant ℚ G a.val a.property
    apply (Ideal.span_mono (show f '' {b | b≠a} ⊆
      (fun b => MvPolynomial.monomial b (1:ℚ)) '' (staircaseBoundary G \ {a.val}) from ?_)) h
    rintro x ⟨b,hb,rfl⟩
    exact ⟨b.val,⟨b.property,fun he => hb (Subtype.ext he)⟩,rfl⟩
  have hspan : Ideal.span (Set.range f)=Ideal.span (Set.range (reductionPresentationGenerator ℚ R)) := by
    rw [span_reductionPresentationGenerator G ℚ R hR,reductionIdeal_eq_staircaseIdeal ℚ G hG h30,
      staircaseIdeal_eq_boundary_span]
    congr 1
    ext x
    constructor
    · rintro ⟨a,rfl⟩; exact ⟨a.val,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
  have hle := homogeneous_generators_card_le G.generators (fun i => (G.positive i).ne')
    f (reductionPresentationGenerator ℚ R) (fun a => factorizationMap G.generators a.val)
    (fun a => monomial_weighted_homogeneous ℚ G.generators a.val) hirred hspan
  simp only [Fintype.card_coe,Fintype.card_option] at hle
  have hboundary := boundary_card_eq_generatorNumber_add_one G
  rw [Nat.card_eq_fintype_card] at hboundary
  omega

end FourGeneratedSemigroups
