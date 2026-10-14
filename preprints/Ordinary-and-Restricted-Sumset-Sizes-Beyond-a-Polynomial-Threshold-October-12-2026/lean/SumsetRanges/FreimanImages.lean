import SumsetRanges.RestrictedPolynomial

open Finset Polynomial
namespace SumsetRanges

section
variable {α β : Type*} [AddCommMonoid α] [AddCommMonoid β]
  [DecidableEq α] [DecidableEq β]

theorem restrictedSums_image (A : Finset α) (φ : α →+ β)
    (hinj : Set.InjOn φ A) (q : ℕ) :
    restrictedSums (A.image φ) q = (restrictedSums A q).image φ := by
  ext y
  constructor
  · intro hy
    obtain ⟨T,hT,hTc,hTy⟩ := mem_restrictedSums.mp hy
    obtain ⟨S,hS,hST⟩ := Finset.subset_image_iff.mp hT
    have hS_inj : Set.InjOn φ S := hinj.mono hS
    have hc : S.card=q := by
      rw [← hTc,← hST,Finset.card_image_of_injOn hS_inj]
    have he : φ (∑ a ∈ S,a)=y := by
      rw [map_sum]
      rw [← hTy,← hST,Finset.sum_image]
      exact hS_inj
    exact Finset.mem_image.mpr ⟨∑ a ∈ S,a,mem_restrictedSums.mpr ⟨S,hS,hc,rfl⟩,he⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hx
    have hS_inj : Set.InjOn φ S := hinj.mono hS
    refine mem_restrictedSums.mpr ⟨S.image φ,Finset.image_subset_image hS,?_,?_⟩
    · rw [Finset.card_image_of_injOn hS_inj,hSc]
    · rw [Finset.sum_image hS_inj,map_sum]

theorem card_restrictedSums_image (A : Finset α) (φ : α →+ β)
    (hinj : Set.InjOn φ A) (q : ℕ) (hsum : Set.InjOn φ (restrictedSums A q)) :
    (restrictedSums (A.image φ) q).card = (restrictedSums A q).card := by
  rw [restrictedSums_image A φ hinj q,Finset.card_image_of_injOn hsum]

omit [DecidableEq α] in
theorem degree_one_sum (A : Finset α) (δ : α →+ ℤ) (hδ : ∀ a∈A, δ a=1)
    (S : Finset α) (hS : S⊆A) : δ (∑ a∈S,a)=(S.card : ℤ) := by
  rw [map_sum]
  have he : ∑ a∈S,δ a = ∑ _a∈S,(1:ℤ) := Finset.sum_congr rfl (fun a ha => hδ a (hS ha))
  rw [he]
  simp

theorem degree_one_restricted_sum (A : Finset α) (δ : α →+ ℤ) (hδ : ∀ a∈A, δ a=1)
    (q : ℕ) (x : α) (hx : x∈restrictedSums A q) : δ x=(q:ℤ) := by
  obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hx
  rw [degree_one_sum A δ hδ S hS,hSc]

omit [DecidableEq α] in
theorem degree_one_zero_not_mem (A : Finset α) (δ : α →+ ℤ) (hδ : ∀ a∈A, δ a=1) : 0∉A := by
  intro h
  have hh := hδ 0 h
  simp at hh

end
end SumsetRanges
