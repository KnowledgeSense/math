import MainTheorems.LocalPermutation.BasisCosets

namespace ResearchMain.LocalPermutation

open Classical Module

variable {F K : Type} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

noncomputable def basisSupport {I : Type} [Fintype I] (b : Basis I F K) : Finset K :=
  Finset.univ.image b

theorem basisSupport_subset (b : Basis (K ≃ₐ[F] K) F K) : basisSupport b ⊆ basisCosets b := by
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
  apply (mem_basisCosets b x).mpr
  refine ⟨i, 0, ?_⟩
  simpa only [map_zero, add_zero] using hi

theorem basisSupport_sum (b : Basis (K ≃ₐ[F] K) F K) (hsum : (∑ i, b i) = 1) :
    (∑ x ∈ basisSupport b, x) = 1 := by
  rw [basisSupport, Finset.sum_image (fun a _ c _ h => b.injective h)]
  exact hsum

theorem basisSupport_map_iff (b : Basis (K ≃ₐ[F] K) F K)
    (hb : ∀ σ i, σ (b i) = b (σ * i)) (σ : K ≃ₐ[F] K) (x : K) :
    σ x ∈ basisSupport b ↔ x ∈ basisSupport b := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨σ⁻¹ * i, Finset.mem_univ _, ?_⟩
    rw [← hb (σ⁻¹) i, hi]
    exact σ.symm_apply_apply x
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    exact ⟨σ * i, Finset.mem_univ _, by rw [← hb σ i, hi]⟩

theorem basisCosets_map_iff (b : Basis (K ≃ₐ[F] K) F K)
    (hb : ∀ σ i, σ (b i) = b (σ * i)) (σ : K ≃ₐ[F] K) (x : K) :
    σ x ∈ basisCosets b ↔ x ∈ basisCosets b := by
  constructor
  · intro h
    obtain ⟨i, c, hc⟩ := (mem_basisCosets b (σ x)).mp h
    apply (mem_basisCosets b x).mpr
    refine ⟨σ⁻¹ * i, c, ?_⟩
    rw [← hb (σ⁻¹) i, ← (σ⁻¹).commutes c, ← map_add, hc]
    exact σ.symm_apply_apply x
  · intro h
    obtain ⟨i, c, hc⟩ := (mem_basisCosets b x).mp h
    apply (mem_basisCosets b (σ x)).mpr
    refine ⟨σ * i, c, ?_⟩
    rw [← hb σ i, ← σ.commutes c, ← map_add, hc]

end ResearchMain.LocalPermutation
