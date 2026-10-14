import EmbeddingDimensionStrata.TopologicalGenerators
import EmbeddingDimensionStrata.CotangentQuotientEquivalence
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The genuine cotangent module before and after conductor truncation -/
noncomputable section
namespace EmbeddingDimensionStrata
open scoped PowerSeries.WithPiTopology
variable {K : Type*} [Field K]

/-- Division by a series of order n lowers a tail cutoff by exactly n. -/
theorem exists_tail_factor_of_hasOrder (f : PowerSeries K) (n : ℕ)
    (hf : HasOrder f n) (c : ℕ) (g : PowerSeries K) (hg : InTail (c+n) g) :
    ∃ h : PowerSeries K, InTail c h ∧ f*h = g := by
  have hf0 : f ≠ 0 := by intro hz; exact hf.2 (by rw [hz, map_zero])
  let u := PowerSeries.Unit_of_divided_by_X_pow_order f
  have hfu : PowerSeries.X ^ n * (u : PowerSeries K) = f := by
    dsimp [u]
    rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hf0]
    convert PowerSeries.X_pow_order_mul_divXPowOrder (f := f) using 1
    rw [(hasOrder_iff_order f n).mp hf, ENat.toNat_natCast]
  obtain ⟨q, hq⟩ := (PowerSeries.X_pow_dvd_iff.mpr hg)
  refine ⟨PowerSeries.X ^ c * ((↑(u⁻¹) : PowerSeries K) * q), ?_, ?_⟩
  · exact PowerSeries.X_pow_dvd_iff.mp ⟨_,rfl⟩
  · rw [← hfu, hq]
    calc
      PowerSeries.X ^ n * ↑u * (PowerSeries.X ^ c * (↑(u⁻¹) * q)) =
          PowerSeries.X ^ c * PowerSeries.X ^ n * (↑u * ↑(u⁻¹)) * q := by ring
      _ = PowerSeries.X ^ (c+n) * q := by simp [pow_add]

/-- Coefficient elimination works for genuine linear subspaces as well. -/
theorem exists_submodule_tail_approximation (M : Submodule K (PowerSeries K))
    (c : ℕ) (hvalues : ∀ n, c ≤ n → ∃ w ∈ M, HasOrder w n)
    (f : PowerSeries K) (hf : InTail c f) (N : ℕ) :
    ∃ g ∈ M, ∀ i < c+N, PowerSeries.coeff i g = PowerSeries.coeff i f := by
  induction N with
  | zero =>
    refine ⟨0, M.zero_mem, ?_⟩
    intro i hi
    simpa using (hf i (by omega)).symm
  | succ N ih =>
    obtain ⟨g,hg,hgf⟩ := ih
    obtain ⟨w,hw,hlow,hlead⟩ := hvalues (c+N) (by omega)
    let a := (PowerSeries.coeff (c+N) f - PowerSeries.coeff (c+N) g) /
      PowerSeries.coeff (c+N) w
    refine ⟨g+a • w, M.add_mem hg (M.smul_mem a hw), ?_⟩
    intro i hi
    by_cases hlt : i < c+N
    · simp only [map_add, map_smul, hlow i hlt, smul_zero, add_zero]
      exact hgf i hlt
    · have heq : i = c+N := by omega
      subst i
      simp only [map_add, map_smul, smul_eq_mul, a]
      rw [div_mul_cancel₀ _ hlead]
      exact add_sub_cancel _ _

variable [TopologicalSpace K]

/-- The constant-coefficient augmentation of the actual complete algebra. -/
def completeAugmentation (S : CompleteGammaSubalgebra (K := K)) : S.val →ₐ[K] K :=
  jetAugmentation.comp ((jetMap K 60).comp S.val.val)

/-- The true zero-constant ideal of the complete algebra, without truncation. -/
def completeAugmentationIdeal (S : CompleteGammaSubalgebra (K := K)) : Ideal S.val :=
  RingHom.ker (completeAugmentation S).toRingHom

@[simp] theorem completeAugmentation_apply (S : CompleteGammaSubalgebra (K := K)) (f : S.val) :
    completeAugmentation S f = PowerSeries.coeff 0 (f : PowerSeries K) := rfl

theorem completeAugmentationIdeal_mem (S : CompleteGammaSubalgebra (K := K)) (f : S.val) :
    f ∈ completeAugmentationIdeal S ↔ PowerSeries.coeff 0 (f : PowerSeries K) = 0 := Iff.rfl

/-- Every sufficiently high tail is literally a product of two elements of the
maximal ideal, not merely a limit of such products. -/
theorem tail_seventy_mem_complete_square (S : CompleteGammaSubalgebra (K := K))
    (f : S.val) (hf : InTail 70 (f : PowerSeries K)) :
    f ∈ completeAugmentationIdeal S ^ 2 := by
  obtain ⟨h,hh,hprod⟩ := exists_tail_factor_of_hasOrder (normalGenerator S 0) 10
    (normalGenerator_normal S 0).hasOrder 60 f hf
  have hhS : h ∈ S.val := tailIdeal_le_of_gamma S.val S.property.1 S.property.2
    ((mem_tailIdeal_iff 60 h).mpr hh)
  have hm1 : (⟨normalGenerator S 0, normalGenerator_mem S 0⟩ : S.val) ∈
      completeAugmentationIdeal S := (normalGenerator_normal S 0).hasOrder.1 0 (by decide)
  have hm2 : (⟨h,hhS⟩ : S.val) ∈ completeAugmentationIdeal S := hh 0 (by omega)
  have hm := Ideal.mul_mem_mul hm1 hm2
  rw [← pow_two] at hm
  convert hm using 1
  exact Subtype.ext hprod.symm

/-- The whole conductor ideal lies in the actual square of the complete
augmentation ideal. This is the key assertion needed for cotangent invariance. -/
theorem tail_sixty_mem_complete_square (S : CompleteGammaSubalgebra (K := K))
    (f : S.val) (hf : InTail 60 (f : PowerSeries K)) :
    f ∈ completeAugmentationIdeal S ^ 2 := by
  let M := ((completeAugmentationIdeal S ^ 2).restrictScalars K).map S.val.val.toLinearMap
  have hv : ∀ n, 60 ≤ n → ∃ w ∈ M, HasOrder w n := by
    intro n hn
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := gamma_decomposable_of_ge_sixty n hn
    obtain ⟨u,hu,hou⟩ := (S.property.2 a).mpr ha
    obtain ⟨v,hv,hov⟩ := (S.property.2 b).mpr hb
    have hum : (⟨u,hu⟩ : S.val) ∈ completeAugmentationIdeal S := hou.1 0 ha0
    have hvm : (⟨v,hv⟩ : S.val) ∈ completeAugmentationIdeal S := hov.1 0 hb0
    refine ⟨u*v, ?_, ?_⟩
    · exact ⟨(⟨u,hu⟩ : S.val) * ⟨v,hv⟩, by
        change (⟨u,hu⟩ : S.val) * ⟨v,hv⟩ ∈ completeAugmentationIdeal S ^ 2
        rw [pow_two]
        exact Ideal.mul_mem_mul hum hvm, rfl⟩
    · rw [hasOrder_iff_order, PowerSeries.order_mul, (hasOrder_iff_order u a).mp hou,
        (hasOrder_iff_order v b).mp hov, hab]
      simp
  obtain ⟨g,hg,hgf⟩ := exists_submodule_tail_approximation M 60 hv f hf 10
  obtain ⟨g',hg',rfl⟩ := hg
  have hdiff : InTail 70 ((f-g' : S.val) : PowerSeries K) := by
    intro i hi
    change PowerSeries.coeff i ((f : PowerSeries K) - (g' : PowerSeries K)) = 0
    have hi' := hgf i hi
    change PowerSeries.coeff i (g' : PowerSeries K) = PowerSeries.coeff i (f : PowerSeries K) at hi'
    rw [map_sub, hi', sub_self]
  have htail := tail_seventy_mem_complete_square S (f-g') hdiff
  have := (completeAugmentationIdeal S ^ 2).add_mem htail hg'
  simpa only [sub_add_cancel] using this


/-- The actual truncation homomorphism, using the canonical normal-coordinate
identification of its image. -/
def completeParameterJetMap (S : CompleteGammaSubalgebra (K := K)) :
    S.val →ₐ[K] parameterJetAlgebra (normalCoordinates S) :=
  ((jetMap K 60).comp S.val.val).codRestrict _ (by
    intro f
    rw [parameterJetAlgebra_normalCoordinates]
    exact ⟨f, f.property, rfl⟩)

theorem completeParameterJetMap_surjective (S : CompleteGammaSubalgebra (K := K)) :
    Function.Surjective (completeParameterJetMap S) := by
  rintro ⟨x,hx⟩
  rw [parameterJetAlgebra_normalCoordinates] at hx
  obtain ⟨f,hf,hfx⟩ := hx
  exact ⟨⟨f,hf⟩, Subtype.ext hfx⟩

theorem augmentationIdeal_comap_completeParameterJetMap
    (S : CompleteGammaSubalgebra (K := K)) :
    (augmentationIdeal (normalCoordinates S)).comap (completeParameterJetMap S) =
      completeAugmentationIdeal S := by
  ext f
  rfl

/-- The kernel assertion is discharged by the proved conductor-square theorem. -/
theorem completeParameterJetMap_ker_le_square (S : CompleteGammaSubalgebra (K := K)) :
    RingHom.ker (completeParameterJetMap S).toRingHom ≤ completeAugmentationIdeal S ^ 2 := by
  intro f hf
  apply tail_sixty_mem_complete_square S f
  apply (jetMap_eq_zero_iff 60 (f : PowerSeries K)).mp
  exact congrArg Subtype.val hf

/-- Truncation induces an equivalence of the actual complete and finite
cotangent modules, with no model space substituted in their definitions. -/
def completeCotangentEquiv (S : CompleteGammaSubalgebra (K := K)) :
    (completeAugmentationIdeal S).Cotangent ≃ₗ[K]
      (augmentationIdeal (normalCoordinates S)).Cotangent :=
  cotangentEquivOfKerLeSquare (completeParameterJetMap S)
    (completeParameterJetMap_surjective S) (completeAugmentationIdeal S)
    (augmentationIdeal (normalCoordinates S))
    (augmentationIdeal_comap_completeParameterJetMap S)
    (completeParameterJetMap_ker_le_square S)

instance completeCotangent_finite (S : CompleteGammaSubalgebra (K := K)) :
    Module.Finite K (completeAugmentationIdeal S).Cotangent := by
  let : Module.Finite K (augmentationIdeal (normalCoordinates S)).Cotangent :=
    NilpotentGenerators.cotangent_finite (parameterAugmentation (normalCoordinates S))
  exact Module.Finite.of_injective (completeCotangentEquiv S).toLinearMap
    (completeCotangentEquiv S).injective

theorem completeCotangent_finrank (S : CompleteGammaSubalgebra (K := K)) :
    Module.finrank K (completeAugmentationIdeal S).Cotangent =
      embeddingDimension (toParameterSpace S) := (completeCotangentEquiv S).finrank_eq

variable [DiscreteTopology K]

/-- The genuine complete-algebra version: its minimum topological generator
number equals the finrank of its own actual maximal-ideal cotangent module. -/
theorem complete_isLeast_generators_own_cotangent
    (S : CompleteGammaSubalgebra (K := K)) :
    IsLeast (topologicalGeneratorNumbers S)
      (Module.finrank K (completeAugmentationIdeal S).Cotangent) := by
  rw [completeCotangent_finrank]
  exact complete_isLeast_topologicalGeneratorNumbers S

end EmbeddingDimensionStrata
