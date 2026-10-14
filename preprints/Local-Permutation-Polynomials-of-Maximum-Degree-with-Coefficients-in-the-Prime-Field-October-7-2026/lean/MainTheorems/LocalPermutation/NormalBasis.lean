import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic

namespace ResearchMain.LocalPermutation

open Classical Module

variable (F L : Type) [Field F] [Field L] [Fintype L] [Algebra F L]

theorem exists_normalized_normalBasis :
    ∃ b : Basis (L ≃ₐ[F] L) F L, (∑ i, b i) = 1 ∧ ∀ σ i, σ (b i) = b (σ * i) := by
  let b₀ := IsGalois.normalBasis F L
  have hmap (σ i : L ≃ₐ[F] L) : σ (b₀ i) = b₀ (σ * i) := by
    change σ (IsGalois.normalBasis F L i) = IsGalois.normalBasis F L (σ * i)
    rw [IsGalois.normalBasis_apply i, IsGalois.normalBasis_apply (σ * i), AlgEquiv.mul_apply]
  have hfixed (σ : L ≃ₐ[F] L) : σ (∑ i, b₀ i) = ∑ i, b₀ i := by
    rw [map_sum]
    simp_rw [hmap]
    exact Equiv.sum_comp (Equiv.mulLeft σ) b₀
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (∑ i, b₀ i)).mpr hfixed
  have hsum : (∑ i, b₀ i) ≠ 0 := by
    intro h
    have hr := congrArg (fun x => b₀.repr x (1 : L ≃ₐ[F] L)) h
    have hs : b₀.repr (∑ i, b₀ i) (1 : L ≃ₐ[F] L) = 1 := by
      simpa only [one_smul] using congrFun (b₀.repr_sum_self (fun _ => (1 : F))) 1
    rw [hs, map_zero, Finsupp.zero_apply] at hr
    exact one_ne_zero hr
  have ht0 : t ≠ 0 := by
    intro h
    apply hsum
    rw [← ht, h, map_zero]
  let u : Fˣ := Units.mk0 t⁻¹ (inv_ne_zero ht0)
  let b := b₀.unitsSMul (fun _ => u)
  have hb (i : L ≃ₐ[F] L) : b i = t⁻¹ • b₀ i := by
    simp only [b, Basis.unitsSMul_apply, Units.smul_def, u, Units.val_mk0]
  refine ⟨b, ?_, ?_⟩
  · simp_rw [hb]
    rw [← Finset.smul_sum, ← ht, Algebra.smul_def]
    have htL : algebraMap F L t ≠ 0 := by simpa only [map_zero] using (algebraMap F L).injective.ne ht0
    simpa only [map_inv₀] using inv_mul_cancel₀ htL
  · intro σ i
    rw [hb, hb, Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes, hmap]

end ResearchMain.LocalPermutation
