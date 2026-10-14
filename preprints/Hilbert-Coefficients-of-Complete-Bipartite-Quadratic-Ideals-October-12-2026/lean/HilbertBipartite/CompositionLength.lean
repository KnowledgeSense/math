import HilbertBipartite.Membership
import HilbertBipartite.StandardCount
import Mathlib.RingTheory.LocalRing.Length

noncomputable section
namespace HilbertBipartite
open MvPolynomial

lemma idealOfVars_eq_constant_kernel (K σ : Type*) [Field K] :
    idealOfVars σ K = RingHom.ker (aeval (fun _ : σ => (0 : K))) := by
  ext f
  have hm := mem_pow_idealOfVars_iff' (σ := σ) (R := K) 1 f
  simp only [pow_one] at hm
  rw [hm, RingHom.mem_ker]
  simp only [aeval_zero', Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_eq]
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h a ha
    have haz : a=0 := (Finsupp.degree_eq_zero_iff a).mp (by omega)
    simpa [haz] using h

lemma bipartiteIdeal_pow_le_constant_kernel (K : Type*) [Field K]
    (p q s : ℕ) (hs : 1 ≤ s) :
    bipartiteIdeal K p q ^ s ≤
      RingHom.ker (aeval (fun _ : Fin p ⊕ Fin q => (0 : K))) := by
  apply (Ideal.pow_le_self (by omega : s ≠ 0)).trans
  rw [bipartiteIdeal_eq_span, Ideal.span_le]
  rintro f (⟨i,rfl⟩ | ⟨⟨i,j⟩,rfl⟩) <;> simp [RingHom.mem_ker]

/-- Constant-term augmentation of the actual power quotient. -/
def quotientAugmentation (K : Type*) [Field K] (p q s : ℕ) (hs : 1 ≤ s) :
    (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (aeval (fun _ => (0 : K)))
    (bipartiteIdeal_pow_le_constant_kernel K p q s hs)

lemma quotientAugmentation_surjective (K : Type*) [Field K] (p q s : ℕ) (hs : 1 ≤ s) :
    Function.Surjective (quotientAugmentation K p q s hs) := by
  intro c
  refine ⟨Ideal.Quotient.mk _ (C c), ?_⟩
  change (aeval (fun _ : Fin p ⊕ Fin q => (0 : K))) (C c) = c
  simp

lemma variable_pow_mem_bipartiteIdeal_pow (K : Type*) [Field K]
    (p q s : ℕ) (i : Fin p ⊕ Fin q) :
    (X i : MvPolynomial _ K)^(2*s) ∈ bipartiteIdeal K p q ^ s := by
  classical
  rw [X_pow_eq_monomial,mem_bipartiteIdeal_pow_iff_support]
  simp only [support_monomial,one_ne_zero,ite_false,Finset.mem_singleton,forall_eq]
  exact ⟨_,squarePower_mem_generatorPowerExponents p q s i,le_rfl⟩

lemma quotientAugmentation_unique_maximal (K : Type*) [Field K]
    (p q s : ℕ) (hs : 1 ≤ s)
    (J : Ideal (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s))
    (hJ : J.IsMaximal) : J = RingHom.ker (quotientAugmentation K p q s hs) := by
  let I := bipartiteIdeal K p q ^ s
  let π := Ideal.Quotient.mk I
  let f : MvPolynomial (Fin p ⊕ Fin q) K →ₐ[K] K :=
    aeval (fun _ : Fin p ⊕ Fin q => (0 : K))
  have hf : Function.Surjective f := by intro c; exact ⟨C c,by simp [f]⟩
  have hm : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let : J.IsMaximal := hJ
  have hpre : (J.comap π).IsMaximal := Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective
  have hle : RingHom.ker f ≤ J.comap π := by
    rw [← idealOfVars_eq_constant_kernel K (Fin p ⊕ Fin q)]
    rw [idealOfVars,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    apply hpre.isPrime.mem_of_pow_mem (2*s)
    change π ((X i)^(2*s)) ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (variable_pow_mem_bipartiteIdeal_pow K p q s i)]
    exact J.zero_mem
  have heq : RingHom.ker f = J.comap π := hm.eq_of_le hpre.ne_top hle
  apply Ideal.comap_injective_of_surjective π Ideal.Quotient.mk_surjective
  rw [← heq]
  ext a
  change f a = 0 ↔ f a = 0
  rfl

/-- The quotient is local, with its unique maximal ideal given by zero constant term. -/
theorem bipartiteQuotientIsLocalRing (K : Type*) [Field K] (p q s : ℕ) (hs : 1 ≤ s) :
    IsLocalRing (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) :=
  IsLocalRing.of_unique_max_ideal ⟨RingHom.ker (quotientAugmentation K p q s hs),
    RingHom.ker_isMaximal_of_surjective _ (quotientAugmentation_surjective K p q s hs),
    fun J hJ => quotientAugmentation_unique_maximal K p q s hs J hJ⟩

/-- A local algebra with residue field `K` has equal module length and vector-space length. -/
lemma localAlgebra_length_eq_finrank (K B : Type*) [Field K] [CommRing B]
    [Algebra K B] [IsLocalRing B] [Module.Finite K B]
    (f : B →ₐ[K] K) (hf : Function.Surjective f) :
    Module.length B B = Module.finrank K B := by
  have hmax : IsLocalRing.maximalIdeal B = RingHom.ker f :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)).symm
  let e : IsLocalRing.ResidueField B ≃ₐ[K] K :=
    (Ideal.quotientEquivAlgOfEq K hmax).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  have hr : Module.length K (IsLocalRing.ResidueField B) = 1 := by
    rw [e.toLinearEquiv.length_eq]
    exact Module.length_eq_one K K
  have hl := IsLocalRing.length_restrictScalars K B B
  have hr' : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField B) = 1 := by
    rw [← Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := K))]
    exact hr
  rw [hr',mul_one,Module.length_eq_finrank] at hl
  exact hl.symm

/-- Literal composition length over the polynomial ring agrees with the proved
standard-monomial vector-space dimension. -/
theorem length_bipartiteIdeal_pow (K : Type*) [Field K] (p q s : ℕ) (hs : 1 ≤ s) :
    Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      (standardExponents p q s).card := by
  let := bipartiteQuotientIsLocalRing K p q s hs
  rw [Module.length_eq_of_surjective
    (R := MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s)
    Ideal.Quotient.mk_surjective]
  rw [localAlgebra_length_eq_finrank K _ (quotientAugmentation K p q s hs)
    (quotientAugmentation_surjective K p q s hs)]
  rw [finrank_bipartiteIdeal_pow]

/-- Theorem 1.1(a): the composition length over the actual polynomial ring. -/
theorem compositionLength_formula (K : Type*) [Field K]
    (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    Module.length (MvPolynomial (Fin p ⊕ Fin q) K)
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      ((2*s+p+q-1).choose (p+q) + correction p q s + correction q p s : ℕ) := by
  rw [length_bipartiteIdeal_pow K p q s hs, standardExponents_card p q s hp hq hs]

end HilbertBipartite
