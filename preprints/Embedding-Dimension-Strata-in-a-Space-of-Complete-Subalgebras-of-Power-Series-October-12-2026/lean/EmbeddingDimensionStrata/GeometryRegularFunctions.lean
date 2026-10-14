import EmbeddingDimensionStrata.GeometryPrincipalOpens
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Prime.Lemmas

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace EmbeddingDimensionStrata
namespace GeometryObstructions
open MvPolynomial

/-- Euclid's lemma in the fraction field: rational functions whose denominators
are powers of either of two nonassociated primes are polynomials. -/
theorem polynomial_of_two_prime_denominators
    {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    {a b : R} (ha : Prime a) (hab : ¬ a ∣ b)
    {z : F} {p q : R} {i j : ℕ}
    (hp : z * algebraMap R F (a ^ i) = algebraMap R F p)
    (hq : z * algebraMap R F (b ^ j) = algebraMap R F q) :
    ∃ r : R, algebraMap R F r = z := by
  have he : p * b ^ j = q * a ^ i := by
    apply IsFractionRing.injective R F
    simp only [map_mul, ← hp, ← hq]
    ring
  have hd0 : a ^ i ∣ p * b ^ j := by
    rw [he]
    exact dvd_mul_left _ _
  have hd : a ^ i ∣ p := ha.pow_dvd_of_dvd_mul_right i
    (fun h => hab (ha.dvd_of_dvd_pow h)) hd0
  obtain ⟨r, hr⟩ := hd
  refine ⟨r, ?_⟩
  have hn : algebraMap R F (a ^ i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (pow_ne_zero i ha.ne_zero)
  apply mul_right_cancel₀ hn
  rw [hp, hr, map_mul, mul_comm]

/-- The units of the ambient polynomial ring are exactly nonzero constants. -/
theorem polynomial_units_are_constants {K ι : Type*} [Field K]
    (p : MvPolynomial ι K) : IsUnit p ↔ ∃ c : K, c ≠ 0 ∧ p = C c := by
  simpa only [isUnit_iff_ne_zero] using
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := p))

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

section SchemeSections
variable (R : CommRingCat) [IsDomain R]

lemma spec_germ_algebraMap (U : (Spec R).Opens) [Nonempty U] (p : R) :
    (Spec R).germToFunctionField U (algebraMap R Γ(Spec R, U) p) =
      algebraMap R (Spec R).functionField p := by
  exact StructureSheaf.algebraMap_germ_apply U _ _ p

lemma spec_germ_restriction {U V : (Spec R).Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (s : Γ(Spec R, U)) :
    (Spec R).germToFunctionField V ((Spec R).presheaf.map (homOfLE h).op s) =
      (Spec R).germToFunctionField U s := by
  exact (Spec R).presheaf.germ_res_apply (homOfLE h) _ _ s

lemma spec_section_denominator (U : (Spec R).Opens) [Nonempty U]
    (a : R) (ha : a ≠ 0) (hU : PrimeSpectrum.basicOpen a ≤ U)
    (s : Γ(Spec R, U)) :
    ∃ (n : ℕ) (p : R), (Spec R).germToFunctionField U s *
      algebraMap R (Spec R).functionField (a ^ n) = algebraMap R (Spec R).functionField p := by
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen a
  have h0 : (⊥ : PrimeSpectrum R) ∈ V := by
    change a ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using ha
  let : Nonempty V := ⟨⟨(⊥ : PrimeSpectrum R), h0⟩⟩
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj a
    (show Γ(Spec R, PrimeSpectrum.basicOpen a) from
      (Spec R).presheaf.map (homOfLE hU).op s)
  refine ⟨n, p, ?_⟩
  have hh := congrArg ((Spec R).germToFunctionField V) hp
  dsimp only [V] at hh
  simp only [map_mul, map_pow] at hh
  rw [spec_germ_restriction R hU, spec_germ_algebraMap, spec_germ_algebraMap] at hh
  simpa only [map_pow] using hh

/-- Hartogs extension for an affine open containing the principal opens of
two nonassociated prime elements. The ring is the actual scheme section ring. -/
theorem spec_sections_bijective_of_two_primes
    (U : (Spec R).Opens) (a b : R) (ha : Prime a) (hb : b ≠ 0) (hab : ¬ a ∣ b)
    (haU : PrimeSpectrum.basicOpen a ≤ U) (hbU : PrimeSpectrum.basicOpen b ≤ U) :
    Function.Bijective (algebraMap R Γ(Spec R, U)) := by
  have h0 : (⊥ : PrimeSpectrum R) ∈ U := haU (by
    change a ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using ha.ne_zero)
  let : Nonempty U := ⟨⟨(⊥ : PrimeSpectrum R), h0⟩⟩
  constructor
  · intro p q hpq
    apply IsFractionRing.injective R (Spec R).functionField
    simpa only [spec_germ_algebraMap] using congrArg ((Spec R).germToFunctionField U) hpq
  · intro s
    obtain ⟨i, p, hp⟩ := spec_section_denominator R U a ha.ne_zero haU s
    obtain ⟨j, q, hq⟩ := spec_section_denominator R U b hb hbU s
    obtain ⟨r, hr⟩ := polynomial_of_two_prime_denominators ha hab hp hq
    refine ⟨r, (Spec R).germToFunctionField_injective U ?_⟩
    simpa only [spec_germ_algebraMap] using hr

omit [IsDomain R] in
/-- An affine open of an affine scheme whose restriction map on functions is
an isomorphism must be the whole scheme. -/
theorem affineOpen_eq_top_of_bijective_sections
    (U : (Spec R).Opens) (hU : IsAffineOpen U)
    (h : Function.Bijective (algebraMap R Γ(Spec R, U))) : U = ⊤ := by
  let f : R ⟶ Γ(Spec R, U) := CommRingCat.ofHom (algebraMap R Γ(Spec R, U))
  let α := (Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  have hi : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr h
  have hi' : IsIso ((Scheme.ΓSpecIso R).inv ≫ α) := hi
  have hα : IsIso α := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso R).inv α
  have hcomp : IsIso (hU.fromSpec ≫ (Spec R).toSpecΓ) := by
    rw [hU.fromSpec_toSpecΓ]
    infer_instance
  have hfrom : IsIso hU.fromSpec := IsIso.of_isIso_comp_right hU.fromSpec (Spec R).toSpecΓ
  have hsurj : Function.Surjective hU.fromSpec :=
    (ConcreteCategory.bijective_of_isIso hU.fromSpec.base).surjective
  apply Opens.ext
  rw [← hU.range_fromSpec, Set.range_eq_univ.mpr hsurj]
  rfl

/-- Nonaffinity is stated using mathlib's ordinary `IsAffineOpen` predicate. -/
theorem not_affineOpen_of_two_primes
    (U : (Spec R).Opens) (hproper : U ≠ ⊤)
    (a b : R) (ha : Prime a) (hb : b ≠ 0) (hab : ¬ a ∣ b)
    (haU : PrimeSpectrum.basicOpen a ≤ U) (hbU : PrimeSpectrum.basicOpen b ≤ U) :
    ¬ IsAffineOpen U := by
  intro hU
  exact hproper (affineOpen_eq_top_of_bijective_sections R U hU
    (spec_sections_bijective_of_two_primes R U a b ha hb hab haU hbU))

end SchemeSections
section PuncturedProductScheme
variable (K : Type*) [Field K] (m : ℕ)

/-- The affine coordinate ring with `m` free parameters and the distinguished
three coordinates. -/
abbrev puncturedAmbientRing := MvPolynomial (Fin m ⊕ Fin 3) K

/-- The ordinary open subscheme `A^m × (A³ \ {0})`, specified inside the
prime spectrum of its ambient polynomial ring. -/
def puncturedProductSchemeOpen :
    (Spec (CommRingCat.of (puncturedAmbientRing K m))).Opens :=
  ⨆ i : Fin 3, PrimeSpectrum.basicOpen (X (Sum.inr i))

instance puncturedProductSectionsAlgebra : Algebra (puncturedAmbientRing K m)
    Γ(Spec (CommRingCat.of (puncturedAmbientRing K m)), puncturedProductSchemeOpen K m) :=
  IsAffineOpen.instAlgebraCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpens
    (R := CommRingCat.of (puncturedAmbientRing K m)) (U := puncturedProductSchemeOpen K m)

/-- On rational points the scheme open has precisely the intended punctured
product, using the standard point-to-prime-ideal map. -/
theorem puncturedProductSchemeOpen_rational_points
    (x : (Fin m ⊕ Fin 3) → K) :
    pointToPoint x ∈ puncturedProductSchemeOpen K m ↔ x ∈ puncturedProduct (K := K) m := by
  simp only [puncturedProductSchemeOpen, Opens.mem_iSup, PrimeSpectrum.mem_basicOpen,
    pointToPoint, mem_vanishingIdeal_singleton_iff, aeval_X, puncturedProduct,
    Set.mem_ofPred_eq]

lemma puncturedProductSchemeOpen_ne_top : puncturedProductSchemeOpen K m ≠ ⊤ := by
  intro h
  let z : PrimeSpectrum (puncturedAmbientRing K m) :=
    pointToPoint (0 : (Fin m ⊕ Fin 3) → K)
  have hz : z ∈ puncturedProductSchemeOpen K m := h ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
  change X (Sum.inr i) ∉ vanishingIdeal K {(0 : (Fin m ⊕ Fin 3) → K)} at hi
  apply hi
  simp

/-- Restriction from the ambient affine space induces an isomorphism onto
the actual structure-sheaf sections of the punctured product. -/
theorem puncturedProduct_sections_bijective :
    Function.Bijective (algebraMap (CommRingCat.of (puncturedAmbientRing K m))
      Γ(Spec (CommRingCat.of (puncturedAmbientRing K m)), puncturedProductSchemeOpen K m)) := by
  apply spec_sections_bijective_of_two_primes _ _
    (X (Sum.inr (0 : Fin 3))) (X (Sum.inr (1 : Fin 3))) X_prime (X_ne_zero _)
  · simp only [X_dvd_X, Sum.inr.injEq, Fin.zero_eq_one_iff]
    decide
  · exact le_iSup (fun i : Fin 3 => PrimeSpectrum.basicOpen (X (Sum.inr i))) 0
  · exact le_iSup (fun i : Fin 3 => PrimeSpectrum.basicOpen (X (Sum.inr i))) 1

/-- The ring of regular functions on the punctured product is the full
polynomial ring, via the canonical restriction map. -/
def puncturedProduct_regularFunctionsEquiv :
    puncturedAmbientRing K m ≃+*
      Γ(Spec (CommRingCat.of (puncturedAmbientRing K m)), puncturedProductSchemeOpen K m) :=
  RingEquiv.ofBijective _ (puncturedProduct_sections_bijective K m)

/-- The punctured product is not affine, for every number of free parameters. -/
theorem puncturedProductScheme_not_affine :
    ¬ IsAffine (puncturedProductSchemeOpen K m).toScheme := by
  intro h
  exact puncturedProductSchemeOpen_ne_top K m
    (affineOpen_eq_top_of_bijective_sections _ _ h (puncturedProduct_sections_bijective K m))

/-- No affine scheme is isomorphic to the punctured product. In particular
this applies to the product of the multiplicative group with affine space. -/
theorem puncturedProductScheme_no_affine_iso (Y : Scheme) [IsAffine Y] :
    IsEmpty ((puncturedProductSchemeOpen K m).toScheme ≅ Y) := by
  constructor
  intro e
  exact puncturedProductScheme_not_affine K m (IsAffine.of_isIso e.hom)

/-- All invertible regular functions on the punctured product are nonzero
constants; this statement is about the actual structure sheaf. -/
theorem puncturedProduct_regular_units_are_constants
    (s : Γ(Spec (CommRingCat.of (puncturedAmbientRing K m)), puncturedProductSchemeOpen K m)) :
    IsUnit s ↔ ∃ c : K, c ≠ 0 ∧
      algebraMap (CommRingCat.of (puncturedAmbientRing K m))
        Γ(Spec (CommRingCat.of (puncturedAmbientRing K m)), puncturedProductSchemeOpen K m)
        (C c) = s := by
  let e := puncturedProduct_regularFunctionsEquiv K m
  constructor
  · intro hs
    have hp := hs.map e.symm.toMonoidHom
    obtain ⟨c, hc, hp⟩ := (polynomial_units_are_constants (e.symm s)).mp hp
    refine ⟨c, hc, ?_⟩
    change e (C c) = s
    rw [← hp, e.apply_symm_apply]
  · rintro ⟨c, hc, rfl⟩
    exact ((polynomial_units_are_constants (C c : puncturedAmbientRing K m)).mpr
      ⟨c, hc, rfl⟩).map _

/-- The usual affine variety `Gₘ × A⁵⁶`, realized as the first-coordinate
principal open of affine 57-space. -/
def predictedFourStratumScheme : Scheme :=
  Scheme.Opens.toScheme (X := Spec (CommRingCat.of (MvPolynomial (Fin 57) K)))
    (PrimeSpectrum.basicOpen (X (0 : Fin 57) : MvPolynomial (Fin 57) K))

instance predictedFourStratumScheme_isAffine : IsAffine (predictedFourStratumScheme K) :=
  IsAffineOpen.Spec_basicOpen _

/-- The algebraic-geometric obstruction in Question 4.8 for the exact dimensions. -/
theorem puncturedProduct54_not_iso_predicted :
    IsEmpty ((puncturedProductSchemeOpen K 54).toScheme ≅ predictedFourStratumScheme K) :=
  puncturedProductScheme_no_affine_iso K 54 _

end PuncturedProductScheme
end GeometryObstructions
end EmbeddingDimensionStrata
