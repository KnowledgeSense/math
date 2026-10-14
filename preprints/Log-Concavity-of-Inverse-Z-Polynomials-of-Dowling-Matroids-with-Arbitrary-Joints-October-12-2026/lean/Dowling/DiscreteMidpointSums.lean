import Dowling.DiscreteMidpointDiagonal

noncomputable section
namespace Dowling
open Finset

 theorem midpointBand_le_supported_sum (H : ℤ→ℝ) (z : ℤ) (n N : ℕ)
    (hH : ∀ i,0≤H i) (hsupp : ∀ i,i < 0 ∨ (N : ℤ) < i → H i=0) :
    midpointBand H z n≤∑ i ∈ range (N+1),H i := by
  let S : Finset ℤ := (range (n+1)).image (fun i : ℕ => (z-(n : ℤ))/2+i)
  let T : Finset ℤ := (range (N+1)).image (fun i : ℕ => (i : ℤ))
  have hS : midpointBand H z n=∑ i ∈ S,H i := by
    dsimp only [S]
    rw [sum_image]
    · rfl
    · intro i hi j hj he
      dsimp at he
      omega
  have hT : (∑ i ∈ range (N+1),H i)=∑ i ∈ T,H i := by
    dsimp only [T]
    rw [sum_image]
    intro i hi j hj he
    dsimp at he
    exact_mod_cast he
  rw [hS,hT]
  have he : (∑ i ∈ S∩T,H i)=∑ i ∈ S,H i := by
    apply sum_subset inter_subset_left
    intro i hi hnot
    apply hsupp
    by_contra hn
    have hi0 : 0 ≤ i := by omega
    have hiN : i ≤ N := by omega
    apply hnot
    apply mem_inter.mpr ⟨hi,?_⟩
    apply mem_image.mpr
    exact ⟨i.toNat,mem_range.mpr (by omega),by omega⟩
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun i _ _=>hH i)

 theorem midpoint_shift_sum (g : ℤ→ℝ) (N i : ℕ) (hi : i ≤ N)
    (hsupp : ∀ j,j < 0 ∨ (N : ℤ) < j → g j=0) :
    (∑ z ∈ range (2*N+1),g ((z : ℤ)-i))=∑ j ∈ range (N+1),g j := by
  apply Finset.sum_bij_ne_zero (fun (z : ℕ) _ _ => ((z : ℤ)-i).toNat)
  · intro z hz hg
    apply mem_range.mpr
    have hbound : ¬((z : ℤ)-i < 0 ∨ (N : ℤ) < (z : ℤ)-i) := by
      intro h
      exact hg (hsupp _ h)
    omega
  · intro z hz hg w hw hgw he
    have hz0 : 0≤(z : ℤ)-i := by
      by_contra h
      exact hg (hsupp _ (Or.inl (by omega)))
    have hw0 : 0≤(w : ℤ)-i := by
      by_contra h
      exact hgw (hsupp _ (Or.inl (by omega)))
    omega
  · intro j hj hgj
    refine ⟨i+j,mem_range.mpr (by have := mem_range.mp hj; omega),?_,?_⟩
    · simpa using hgj
    · omega
  · intro z hz hg
    have hz0 : 0≤(z : ℤ)-i := by
      by_contra h
      exact hg (hsupp _ (Or.inl (by omega)))
    congr 1
    omega

 theorem midpoint_convolution_sum (f g : ℤ→ℝ) (N : ℕ)
    (hsupp : ∀ j,j < 0 ∨ (N : ℤ) < j → g j=0) :
    (∑ z ∈ range (2*N+1),∑ i ∈ range (N+1),f i*g ((z : ℤ)-i))=
      (∑ i ∈ range (N+1),f i)*(∑ j ∈ range (N+1),g j) := by
  rw [sum_comm,Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum,midpoint_shift_sum g N i (by have := mem_range.mp hi; omega) hsupp]

end Dowling
