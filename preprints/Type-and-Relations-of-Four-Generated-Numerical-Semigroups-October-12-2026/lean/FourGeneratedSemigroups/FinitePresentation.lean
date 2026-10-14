import FourGeneratedSemigroups.PresentationIdeal
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section
namespace FourGeneratedSemigroups

/-- Finite generation of the actual binomial kernel gives a finite semigroup presentation. -/
theorem exists_presentation (d : Fin 4 → ℕ) :
    ∃ R : Finset (Factorization × Factorization), IsPresentation d R := by
  classical
  let : IsNoetherianRing ℚ := ⟨fun I => by
    rcases Ideal.eq_bot_or_top I with h | h
    · rw [h]; exact Submodule.fg_bot
    · rw [h]; exact ⟨{1},by simp⟩⟩
  have hfg := (Ideal.span (relationBinomials ℚ d)).fg_of_isNoetherianRing
  obtain ⟨G,hG,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hg : ∀ g : G, ∃ a b : Factorization,
      factorizationMap d a=factorizationMap d b ∧
      g.val=MvPolynomial.monomial a (1 : ℚ)-MvPolynomial.monomial b 1 := by
    intro g
    exact hG g.property
  choose a b hab he using hg
  let R : Finset (Factorization × Factorization) := Finset.univ.image (fun g : G => (a g,b g))
  have hset : presentationBinomials ℚ R = (G : Set (MvPolynomial (Fin 4) ℚ)) := by
    ext f
    constructor
    · rintro ⟨r,hr,rfl⟩
      obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hr
      simp [← he g]
    · intro hf
      let g : G := ⟨f,hf⟩
      refine ⟨(a g,b g),Finset.mem_image.mpr ⟨g,Finset.mem_univ _,rfl⟩,?_⟩
      exact (he g).symm
  refine ⟨R,(isPresentation_iff_definingIdeal_eq_span ℚ d R).mpr ?_⟩
  rw [hset,definingIdeal_eq_binomial_span]
  exact hspan

/-- At least one cardinality of a finite presentation exists. -/
theorem exists_presentation_card (d : Fin 4 → ℕ) :
    ∃ n : ℕ, ∃ R : Finset (Factorization × Factorization), IsPresentation d R ∧ R.card=n := by
  obtain ⟨R,hR⟩ := exists_presentation d
  exact ⟨R.card,R,hR,rfl⟩

/-- The minimum number of relations in a presentation of the actual factorization congruence. -/
def presentationNumber (d : Fin 4 → ℕ) : ℕ := by
  classical
  exact Nat.find (exists_presentation_card d)

 theorem presentationNumber_le (d : Fin 4 → ℕ)
    (R : Finset (Factorization × Factorization)) (hR : IsPresentation d R) :
    presentationNumber d ≤ R.card := by
  classical
  exact Nat.find_min' (exists_presentation_card d) ⟨R,hR,rfl⟩

/-- The minimum is attained by a genuine inclusion-minimal presentation. -/
theorem exists_minimalPresentation_card (d : Fin 4 → ℕ) :
    ∃ R : Finset (Factorization × Factorization),
      IsMinimalPresentation d R ∧ R.card=presentationNumber d := by
  classical
  obtain ⟨R,hR,hcard⟩ := Nat.find_spec (exists_presentation_card d)
  refine ⟨R,⟨hR,?_⟩,hcard⟩
  intro R' hsub hR'
  have hle := presentationNumber_le d R' hR'
  have hlt := Finset.card_lt_card hsub
  change R.card=presentationNumber d at hcard
  omega

end FourGeneratedSemigroups
