import FourGeneratedSemigroups.FinitePresentation
import FourGeneratedSemigroups.HomogeneousGeneratorComparison

noncomputable section
namespace FourGeneratedSemigroups

/-- The binomials of a presentation, indexed by its relation set. -/
def presentationFamily (K : Type*) [Field K]
    (R : Finset (Factorization × Factorization)) (r : R) : MvPolynomial (Fin 4) K :=
  MvPolynomial.monomial r.val.1 1 - MvPolynomial.monomial r.val.2 1

lemma presentationFamily_range (K : Type*) [Field K]
    (R : Finset (Factorization × Factorization)) :
    Set.range (presentationFamily K R) = presentationBinomials K R := by
  ext f
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r.val, r.property, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

lemma factorizationMap_eq_weight (d : Fin 4 → ℕ) (a : Factorization) :
    factorizationMap d a = Finsupp.weight d a := by
  simp [factorizationMap, Finsupp.weight_apply, Finsupp.sum_fintype, smul_eq_mul]

lemma presentationFamily_homogeneous (K : Type*) [Field K]
    (d : Fin 4 → ℕ) (R : Finset (Factorization × Factorization))
    (hR : IsPresentation d R) (r : R) :
    MvPolynomial.IsWeightedHomogeneous d (presentationFamily K R r)
      (factorizationMap d r.val.1) := by
  have he : factorizationMap d r.val.1 = factorizationMap d r.val.2 := by
    have hh : addConGen (fun a b => (a, b) ∈ R) r.val.1 r.val.2 :=
      AddConGen.Rel.of _ _ r.property
    rw [hR] at hh
    exact hh
  apply MvPolynomial.IsWeightedHomogeneous.sub
  · exact MvPolynomial.isWeightedHomogeneous_monomial d _ 1
      (factorizationMap_eq_weight d _).symm
  · exact MvPolynomial.isWeightedHomogeneous_monomial d _ 1
      ((factorizationMap_eq_weight d _).symm.trans he.symm)

lemma presentationFamily_others (K : Type*) [Field K]
    (R : Finset (Factorization × Factorization)) (r : R) :
    presentationFamily K R '' {j | j ≠ r} = presentationBinomials K (R.erase r.val) := by
  classical
  ext f
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.val, Finset.mem_erase.mpr ⟨?_, j.property⟩, rfl⟩
    exact fun he => hj (Subtype.ext he)
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    refine ⟨⟨j, hj⟩, ?_, rfl⟩
    exact fun he => hne (congrArg Subtype.val he)

/-- Inclusion-minimal congruence presentations give irredundant polynomial
binomial generators; the converse ideal/congruence bridge prevents cancellation
of a presentation relation. -/
theorem minimalPresentation_family_irredundant (K : Type*) [Field K]
    (d : Fin 4 → ℕ) (R : Finset (Factorization × Factorization))
    (hR : IsMinimalPresentation d R) (r : R) :
    presentationFamily K R r ∉
      Ideal.span (presentationFamily K R '' {j | j ≠ r}) := by
  classical
  intro hred
  rw [presentationFamily_others] at hred
  apply hR.2 (R.erase r.val) (Finset.erase_ssubset r.property)
  apply (isPresentation_iff_definingIdeal_eq_span K d _).mpr
  rw [definingIdeal_eq_presentation_span K d R hR.1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    by_cases he : j = r.val
    · subst j
      exact hred
    · exact Ideal.subset_span ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩, rfl⟩
  · apply Ideal.span_mono
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_of_mem_erase hj, rfl⟩

/-- For positive weights, every inclusion-minimal presentation has no more
relations than any finite presentation of the same semigroup. -/
theorem minimalPresentation_card_le (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i)
    (R T : Finset (Factorization × Factorization))
    (hR : IsMinimalPresentation d R) (hT : IsPresentation d T) : R.card ≤ T.card := by
  have hh := homogeneous_generators_card_le d (fun i => Nat.ne_of_gt (hd i))
    (presentationFamily ℚ R) (presentationFamily ℚ T)
    (fun r => factorizationMap d r.val.1)
    (presentationFamily_homogeneous ℚ d R hR.1)
    (minimalPresentation_family_irredundant ℚ d R hR) (by
      rw [presentationFamily_range, presentationFamily_range,
        ← definingIdeal_eq_presentation_span ℚ d R hR.1,
        ← definingIdeal_eq_presentation_span ℚ d T hT])
  simpa only [Fintype.card_coe] using hh

/-- All inclusion-minimal presentations have the minimum presentation size. -/
theorem minimalPresentation_card_eq_presentationNumber (d : Fin 4 → ℕ)
    (hd : ∀ i, 0 < d i) (R : Finset (Factorization × Factorization))
    (hR : IsMinimalPresentation d R) : R.card = presentationNumber d := by
  obtain ⟨T, hT, hcard⟩ := exists_minimalPresentation_card d
  apply Nat.le_antisymm
  · rw [← hcard]
    exact minimalPresentation_card_le d hd R T hR hT.1
  · exact presentationNumber_le d R hR.1

/-- Cardinality is invariant among inclusion-minimal presentations. -/
theorem minimalPresentation_card_eq (d : Fin 4 → ℕ) (hd : ∀ i, 0 < d i)
    (R T : Finset (Factorization × Factorization))
    (hR : IsMinimalPresentation d R) (hT : IsMinimalPresentation d T) :
    R.card = T.card := by
  rw [minimalPresentation_card_eq_presentationNumber d hd R hR,
    minimalPresentation_card_eq_presentationNumber d hd T hT]

end FourGeneratedSemigroups
